"""
Unicode operators and constructors for `CategoricalInterventions.jl`.

These provide concise algebraic syntax for intervention programs. Type the LaTeX
name followed by TAB in the Julia REPL to enter most of these symbols.

| Symbol | LaTeX | Operation | Example |
|--------|-------|-----------|---------|
| `ℙ` | `\\bbP` | Parameter target | `ℙ(:β)` |
| `𝕊` | `\\bbS` | State target | `𝕊(:I)` |
| `𝕀` | `\\bbI` | Half-open interval | `𝕀(10, 30)` |
| `ι` | `\\iota` | Intervention atom | `ι(:closure, β, τ, κ(0.6))` |
| `Π` | `\\Pi` | Intervention program | `Π(atom1, atom2)` |
| `≜` | `\\triangleq` | Absolute assignment | `≜(0.25)` |
| `δ` | `\\delta` | Additive effect | `δ(5.0)` |
| `κ` | `\\kappa` | Multiplicative scale | `κ(0.6)` |
| `⊕` | `\\oplus` | Program composition | `lockdown ⊕ vaccination` |
| `⊙` | `\\odot` | Apply program | `program ⊙ baseline` |
| `∩` | `\\cap` | Interval intersection | `𝕀(1, 3) ∩ 𝕀(2, 4)` |
| `∈` | `\\in` | Time containment | `10 ∈ 𝕀(10, 30)` |
"""

_target_name(name::Symbol) = name
_target_name(name::AbstractString) = Symbol(name)

"""
    ℙ(name; value_type=Any, algebra=RejectOverlap())

Construct a parameter target. Type `\\bbP<TAB>`.
"""
ℙ(name; value_type::Type=Any, algebra::AbstractCombinationAlgebra=RejectOverlap()) =
    Target(_target_name(name); kind=Parameter, value_type, algebra)

"""
    𝕊(name; value_type=Any, algebra=RejectOverlap())

Construct a state target. Type `\\bbS<TAB>`.
"""
𝕊(name; value_type::Type=Any, algebra::AbstractCombinationAlgebra=RejectOverlap()) =
    Target(_target_name(name); kind=State, value_type, algebra)

"""
    𝕀(start, stop)

Construct a half-open intervention support interval `[start, stop)`.
Type `\\bbI<TAB>`.
"""
𝕀(start, stop) = Interval(start, stop)

"""
    ι(id, target, support, effect; metadata=Dict())

Construct an intervention atom. Type `\\iota<TAB>`.
"""
ι(id::Symbol, target::Target, support::Interval, effect::AbstractEffect;
  metadata::Dict{Symbol,Any}=Dict{Symbol,Any}()) =
    InterventionAtom(id, target, support, effect; metadata)

"""
    Π(atoms...)

Construct an intervention program. Type `\\Pi<TAB>`.
"""
Π(atoms::InterventionAtom...) = InterventionProgram(atoms...)
Π(atoms::AbstractVector{<:InterventionAtom}) = InterventionProgram(atoms)

"""
    ≜(value)

Construct an absolute assignment effect, equivalent to `SetValue(value)`.
Type `\\triangleq<TAB>`.
"""
≜(value) = SetValue(value)

"""
    δ(delta)

Construct an additive effect, equivalent to `Add(delta)`. Type `\\delta<TAB>`.
"""
δ(delta) = Add(delta)

"""
    κ(factor)

Construct a multiplicative scaling effect, equivalent to `Scale(factor)`.
Type `\\kappa<TAB>`.
"""
κ(factor) = Scale(factor)

"""
    left ⊕ right

Compose intervention programs or atoms. Type `\\oplus<TAB>`.

Composition concatenates atoms and then applies the package conflict rules:
different targets compose freely; same-target overlaps require an explicit
combination algebra.
"""
⊕(left::InterventionProgram, right::InterventionProgram) =
    compose_interventions(left, right)
⊕(left::InterventionAtom, right::InterventionAtom) =
    compose_interventions(InterventionProgram(left), InterventionProgram(right))
⊕(left::InterventionProgram, right::InterventionAtom) =
    compose_interventions(left, InterventionProgram(right))
⊕(left::InterventionAtom, right::InterventionProgram) =
    compose_interventions(InterventionProgram(left), right)

"""
    program ⊙ baseline
    program ⊙ (baseline, times)

Apply an intervention program. Type `\\odot<TAB>`.

With a baseline dictionary, this is `apply_interventions`. With a tuple of
`(baseline, times)`, this is `apply_discrete`.
"""
⊙(program::InterventionProgram, baseline::Dict) = apply_interventions(program, baseline)
⊙(atom::InterventionAtom, baseline::Dict) =
    apply_interventions(InterventionProgram(atom), baseline)
⊙(program::InterventionProgram, schedule::Tuple{<:Dict,<:AbstractVector}) =
    apply_discrete(program, schedule[1], schedule[2])
⊙(atom::InterventionAtom, schedule::Tuple{<:Dict,<:AbstractVector}) =
    apply_discrete(InterventionProgram(atom), schedule[1], schedule[2])

Base.in(t, I::Interval) = contains_time(I, t)
Base.:∩(left::Interval, right::Interval) = intersection(left, right)
