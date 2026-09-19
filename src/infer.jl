"""
Inference: recover a program from a baseline schedule and an observed one.

For a target with a multiplicative (or set-then-scale) algebra the observed
schedule is decomposed into maximal runs of constant ratio; for an additive
algebra into runs of constant difference. Applying the inferred program to the
baseline returns the observed schedule on the grid (Lean: `infer_putget`).
"""

_relation(::Union{Multiplicative,Affine{Multiplicative}}) = (:ratio, (o, b) -> o / b, r -> Scale(r), 1)
_relation(::Union{Additive,Affine{Additive}}) = (:difference, (o, b) -> o - b, d -> Add(d), 0)
_relation(alg) = error("infer supports Multiplicative and Additive algebras (or Affine over them); got $alg")

"""
    infer(baseline, observed, times; space, kind=Parameter, atol=1e-10) -> Program

`baseline` and `observed` are `Dict{Symbol,<:AbstractVector}` on the grid
`times` (a range or sorted vector). Returns one atom per maximal run where the
observed value differs from baseline by a constant ratio or difference. The
last span ends one grid step after the last grid time.
"""
function infer(baseline::Dict{Symbol,<:AbstractVector}, observed::Dict{Symbol,<:AbstractVector},
               times::AbstractVector; space::TargetSpace, kind::TargetKind=Parameter, atol=1e-10)
    n = length(times)
    n >= 1 || error("empty grid")
    step_ = n >= 2 ? times[end] - times[end - 1] : one(eltype(times))
    stop_of(i) = i < n ? times[i + 1] : times[n] + step_
    atoms = Atom[]
    for (name, obs) in observed
        haskey(baseline, name) || error("baseline missing for $name")
        base = baseline[name]
        length(base) == length(obs) == n || error("schedules must have length $(n)")
        target = Target(name, kind)
        _, rel, make, unit = _relation(algebra(space, target))
        i = 1
        run = 0
        while i <= n
            r = rel(obs[i], base[i])
            if isapprox(r, unit; atol)
                i += 1
                continue
            end
            j = i
            while j + 1 <= n && isapprox(rel(obs[j + 1], base[j + 1]), r; atol)
                j += 1
            end
            run += 1
            push!(atoms, Atom(Symbol(name, "_", run), target, Span(times[i], stop_of(j)), make(r)))
            i = j + 1
        end
    end
    return Program(atoms, space)
end
