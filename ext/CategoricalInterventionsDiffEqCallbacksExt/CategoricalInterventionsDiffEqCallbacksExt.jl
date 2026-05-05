module CategoricalInterventionsDiffEqCallbacksExt

using DiffEqCallbacks
using CategoricalInterventions

"""
    to_callback(program, indexing; baseline_p=nothing, save_positions=(true, true), check=true)

Lower an intervention program to a `DiffEqCallbacks.PresetTimeCallback`.
The callback mutates `integrator.p` for parameter/process/observation targets and
`integrator.u` for state targets. If `baseline_p` is not supplied, each solve's
initial parameter vector is captured from its integrator and used as that solve's
baseline for interval parameter effects.
"""
function CategoricalInterventions.to_callback(
    program::InterventionProgram,
    indexing::PetriIndexing;
    baseline_p=nothing,
    save_positions=(true, true),
    check::Bool=true,
)
    if check
        cs = conflicts(program)
        isempty(cs) || throw(InterventionConflictError(cs))
    end

    times = callback_times(program)
    has_parameter_effects = any(atom.target.kind != State for atom in program.atoms)
    explicit_baseline = baseline_p === nothing ? nothing : copy(baseline_p)
    integrator_baselines = IdDict{Any,Any}()

    function baseline_for!(integrator)
        explicit_baseline !== nothing && return explicit_baseline
        return get!(integrator_baselines, integrator) do
            copy(integrator.p)
        end
    end

    function initialize!(cb, u, t, integrator)
        if has_parameter_effects
            p_baseline = baseline_for!(integrator)
            apply_parameter_effects!(integrator.p, program, indexing, p_baseline, t; check=false)
        end
        return nothing
    end

    function affect!(integrator)
        p_baseline = nothing
        if has_parameter_effects
            p_baseline = baseline_for!(integrator)
        end
        apply_to_integrator!(integrator, program, indexing, integrator.t;
                             baseline_p=p_baseline, check=false)
        return nothing
    end

    return DiffEqCallbacks.PresetTimeCallback(times, affect!;
                                              initialize=initialize!,
                                              save_positions=save_positions)
end

end # module
