module CategoricalInterventionsPlotsExt

using Plots
using CategoricalInterventions
const CI = CategoricalInterventions

"""
    plot_program(program; kwargs...)

Gantt chart: one row per target, a bar per span atom and a marker per pulse.
"""
function CI.plot_program(p::Program; kwargs...)
    names = unique([t.name for a in p.atoms for t in CI.atom_targets(a)])
    row = Dict(n => i for (i, n) in enumerate(names))
    plt = Plots.plot(; yticks=(1:length(names), string.(names)), ylims=(0.4, length(names) + 0.6),
                     xlabel="time", legend=false, grid=false, kwargs...)
    for a in p.atoms
        y = row[a.target.name]
        if a.support isa Span
            Plots.plot!(plt, Plots.Shape([a.support.lo, a.support.hi, a.support.hi, a.support.lo],
                                         [y - 0.35, y - 0.35, y + 0.35, y + 0.35]); fillalpha=0.5)
            Plots.annotate!(plt, (a.support.lo + a.support.hi) / 2, y, Plots.text(string(a.id), 7))
        else
            Plots.scatter!(plt, [a.support.t], [y]; marker=:diamond, markersize=7)
            Plots.annotate!(plt, a.support.t, y + 0.3, Plots.text(string(a.id), 7))
            if a.effect isa Transfer
                Plots.scatter!(plt, [a.support.t], [row[a.effect.to]]; marker=:diamond, markersize=7)
            end
        end
    end
    return plt
end
Plots.plot(p::Program; kwargs...) = CI.plot_program(p; kwargs...)

end # module
