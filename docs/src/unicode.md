# [Unicode syntax](@id unicode-syntax)

```@meta
CurrentModule = CategoricalInterventions
```

The package provides ContACT.jl-style Unicode shorthand for common constructors
and operations. These aliases are thin wrappers over the standard API.

| Symbol | LaTeX tab completion | Meaning |
| --- | --- | --- |
| [`ℙ`](@ref) | `\bbP<TAB>` | parameter target |
| [`𝕊`](@ref) | `\bbS<TAB>` | state target |
| [`𝕀`](@ref) | `\bbI<TAB>` | half-open interval |
| [`ι`](@ref) | `\iota<TAB>` | intervention atom |
| [`Π`](@ref) | `\Pi<TAB>` | intervention program |
| [`≜`](@ref) | `\triangleq<TAB>` | absolute assignment effect |
| [`δ`](@ref) | `\delta<TAB>` | additive effect |
| [`κ`](@ref) | `\kappa<TAB>` | multiplicative scale effect |
| [`⊕`](@ref) | `\oplus<TAB>` | program or atom composition |
| [`⊙`](@ref) | `\odot<TAB>` | apply a program |

Example:

```julia
β = ℙ(:beta; value_type=Float64, algebra=MultiplicativeAlgebra())
closure = ι(:closure, β, 𝕀(10.0, 30.0), κ(0.6))
program = Π(closure)
program ⊙ Dict(:beta => 0.30)
```

The package also extends interval containment and intersection:

```julia
10.0 ∈ 𝕀(10.0, 30.0)
𝕀(10.0, 30.0) ∩ 𝕀(20.0, 40.0)
```

## Unicode API

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
