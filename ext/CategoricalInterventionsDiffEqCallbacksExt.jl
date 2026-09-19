module CategoricalInterventionsDiffEqCallbacksExt

using DiffEqCallbacks
using SciMLBase
using CategoricalInterventions
const CI = CategoricalInterventions

"""
    to_callback(program, model; baseline_p=nothing, save_positions=(true, true), check=true)

Lower a program to a `PresetTimeCallback`. Parameter-like targets are reset to
baseline and re-applied at every span endpoint; pulses mutate `integrator.u` at
their instants. The baseline is `baseline_p` if given, otherwise captured from
the integrator when the solve starts and released when it ends, so one callback
can be reused across solves.
"""
function CI.to_callback(program::Program, m::Union{Model,Indexing};
                        baseline_p=nothing, save_positions=(true, true), check::Bool=true)
    check && CI.check_conflicts(program)
    m isa Model && CI.check_targets(program, m)
    any(a -> a.effect isa Flow, program.atoms) &&
        error("Program contains Flow atoms; call `augment(model, program)` first (or use `simulate`)")
    times = CI.event_times(program)
    has_param = any(CI.is_parameter_like(t) for a in program.atoms for t in CI.atom_targets(a))
    explicit = baseline_p !== nothing
    baseline = Ref{Any}(explicit ? copy(baseline_p) : nothing)

    function initialize!(cb, u, t, integrator)
        explicit || (baseline[] = copy(integrator.p))
        has_param && CI.apply_parameter_effects!(integrator.p, program, m, baseline[], t; check=false)
        return nothing
    end
    function affect!(integrator)
        CI.apply_to_integrator!(integrator, program, m, integrator.t;
                                baseline_p=has_param ? baseline[] : nothing, check=false)
        return nothing
    end
    function finalize!(cb, u, t, integrator)
        explicit || (baseline[] = nothing)
        return nothing
    end
    return DiffEqCallbacks.PresetTimeCallback(times, affect!; initialize=initialize!,
                                              finalize=finalize!, save_positions=save_positions)
end

"""
    simulate(model, program; u0, p0, tspan, alg=nothing, kwargs...)

Realise flows by augmentation, lower the program to a callback, build the
`ODEProblem` (or `DiscreteProblem` for a discrete model) from the model's
dynamics, and solve. Extra keywords go to `solve`.
"""
function CI.simulate(m::Model, program::Program; u0, p0, tspan, alg=nothing, kwargs...)
    if any(a -> a.effect isa Flow, program.atoms)
        aug = CI.augment(m, program)
        m, program, p0 = aug.model, aug.program, aug.extend(p0)
    end
    capture = get(m.metadata, :baseline_from_integrator, false)
    cb = CI.to_callback(program, m; baseline_p=capture ? nothing : p0)
    prob = m.kind == :discrete ? SciMLBase.DiscreteProblem(m.dynamics, u0, tspan, p0) :
                                 SciMLBase.ODEProblem(m.dynamics, u0, tspan, p0)
    return alg === nothing ? SciMLBase.solve(prob; callback=cb, kwargs...) :
                             SciMLBase.solve(prob, alg; callback=cb, kwargs...)
end

end # module
