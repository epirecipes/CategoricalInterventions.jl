# [Unicode syntax](@id unicode-syntax)

```@meta
CurrentModule = CategoricalInterventions
```

Thin aliases over the plain API. Type the LaTeX name and TAB.

| Symbol | LaTeX | Meaning |
|---|---|---|
| [`ℙ`](@ref) | `\bbP` | parameter target |
| [`𝕊`](@ref) | `\bbS` | state target |
| [`𝕀`](@ref) | `\bbI` | span |
| [`ι`](@ref) | `\iota` | atom |
| [`Π`](@ref) | `\Pi` | program |
| [`≜`](@ref), [`δ`](@ref), [`κ`](@ref) | `\triangleq`, `\delta`, `\kappa` | set, add, scale |
| [`⊕`](@ref) | `\oplus` | compose |
| [`⊙`](@ref) | `\odot` | apply |

```julia
β = ℙ(:beta)
closure = ι(:closure, β, 𝕀(10, 30), κ(0.6))
Π(closure) ⊙ Dict(:beta => 0.30)
```

```@docs
ℙ
𝕊
𝕀
ι
Π
≜
δ
κ
⊕
⊙
```
