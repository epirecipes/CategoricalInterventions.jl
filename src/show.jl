"""
Explanations and tables.
"""

function _fmt(x)
    x isa AbstractFloat ? string(round(x; sigdigits=4)) : string(x)
end

"""
    explain(program; baseline=nothing, io=stdout)

Print the epoch table of a program in plain language: for each epoch, which
atoms are active and the combined effect (or value, if a baseline is given)
per target; then the pulses.
"""
function explain(p::Program; baseline=nothing, io::IO=stdout)
    cs = conflicts(p)
    if !isempty(cs)
        println(io, "Program has ", length(cs), " conflict(s):")
        for c in cs
            println(io, "  - ", c)
        end
        return nothing
    end
    es = epochs(p)
    if isempty(es)
        println(io, "No span interventions.")
    else
        println(io, "Epochs:")
        for e in es
            ids = join(string.(getfield.(e.atoms, :id)), ", ")
            println(io, "  ", e.support, "  ", ids)
            for t in sort(collect(keys(e.effects)); by=x -> string(x.name))
                eff = e.effects[t]
                if baseline !== nothing && haskey(baseline, t.name) && eff !== nothing
                    v0 = baseline[t.name]
                    println(io, "      ", t.name, ": ", _fmt(v0), " → ", _fmt(apply_effect(eff, v0)), "  (", eff, ")")
                else
                    println(io, "      ", t.name, ": ", eff === nothing ? "CONFLICT" : string(eff))
                end
            end
        end
    end
    pulses = [a for a in p.atoms if a.support isa Instant]
    if !isempty(pulses)
        println(io, "Pulses:")
        for a in sort(pulses; by=a -> a.support.t)
            println(io, "  at ", a.support.t, "  ", a.id, ": ", a.target.name, " ", a.effect)
        end
    end
    flows = [a for a in p.atoms if a.effect isa Flow]
    if !isempty(flows)
        println(io, "Flows (realised by augment):")
        for a in flows
            println(io, "  ", a.support, "  ", a.id, ": ", a.target.name, " ", a.effect)
        end
    end
    return nothing
end

"""
    table(program) -> Vector{NamedTuple}

The epoch table as rows `(start, stop, target, effect, atoms)`.
"""
function table(p::Program)
    rows = NamedTuple[]
    for e in epochs(p; check=false), t in sort(collect(keys(e.effects)); by=x -> string(x.name))
        push!(rows, (start=e.support.lo, stop=e.support.hi, target=t.name,
                     effect=e.effects[t] === nothing ? "CONFLICT" : string(e.effects[t]),
                     atoms=[a.id for a in e.atoms if t in atom_targets(a)]))
    end
    return rows
end

"""
    plot(program)

Gantt chart of supports by target. Load Plots.jl to activate.
"""
function plot_program end
