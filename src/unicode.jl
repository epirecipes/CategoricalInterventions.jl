"""
Unicode shorthand (ContACT.jl style). Type the LaTeX name and TAB.

| Symbol | LaTeX | Meaning |
|---|---|---|
| `ℙ(:β)` | `\\bbP` | parameter target |
| `𝕊(:I)` | `\\bbS` | state target |
| `𝕀(10, 30)` | `\\bbI` | span `[10, 30)` |
| `ι(:id, target, support, effect)` | `\\iota` | atom |
| `Π(atoms...)` | `\\Pi` | program |
| `≜(x)`, `δ(x)`, `κ(x)` | `\\triangleq`, `\\delta`, `\\kappa` | set, add, scale |
| `p ⊕ q` | `\\oplus` | compose |
| `p ⊙ baseline` | `\\odot` | apply |
"""

_kw_warn(kw) = isempty(kw) || @warn "value_type and algebra are declared on the model or TargetSpace, not on targets; ignored" maxlog=1

"""ℙ(name): parameter target. Type `\\bbP<TAB>`."""
ℙ(name; kw...) = (_kw_warn(kw); Target(Symbol(name), Parameter))
"""𝕊(name): state target. Type `\\bbS<TAB>`."""
𝕊(name; kw...) = (_kw_warn(kw); Target(Symbol(name), State))
"""𝕀(lo, hi): span `[lo, hi)`. Type `\\bbI<TAB>`."""
𝕀(lo, hi) = Span(lo, hi)
"""ι(id, target, support, effect): atom. Type `\\iota<TAB>`."""
ι(id::Symbol, target::Target, support::AbstractSupport, effect::AbstractEffect; metadata=Dict{Symbol,Any}()) =
    InterventionAtom(id, target, support, effect; metadata=Dict{Symbol,Any}(metadata))
"""Π(atoms...): program. Type `\\Pi<TAB>`."""
Π(atoms::Atom...; space=TargetSpace()) = Program(collect(atoms); space)
Π(atoms::AbstractVector{<:Atom}; space=TargetSpace()) = Program(atoms; space)
"""≜(value): absolute assignment. Type `\\triangleq<TAB>`."""
≜(value) = SetValue(value)
"""δ(delta): additive effect. Type `\\delta<TAB>`."""
δ(delta) = Add(delta)
"""κ(factor): multiplicative effect. Type `\\kappa<TAB>`."""
κ(factor) = Scale(factor)
"""p ⊕ q: compose programs or atoms. Type `\\oplus<TAB>`."""
⊕(a, b) = compose(a, b)
"""p ⊙ baseline, p ⊙ (baseline, times): apply. Type `\\odot<TAB>`."""
⊙(p::Program, baseline::Dict) = apply(p, baseline)
⊙(a::Atom, baseline::Dict) = apply(Program(a), baseline)
⊙(p::Program, schedule::Tuple{<:Dict,<:AbstractVector}) = apply(p, schedule[1], schedule[2])
⊙(a::Atom, schedule::Tuple{<:Dict,<:AbstractVector}) = apply(Program(a), schedule[1], schedule[2])
