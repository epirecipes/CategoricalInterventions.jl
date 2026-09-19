"""
Programs as narratives.

The persistent narrative of a program sends a closed interval `[lo, hi]` to the
atoms in force *throughout* it; the cumulative narrative sends it to the atoms in
force *at some time* in it. The first is a sheaf and the second a cosheaf for the
interval site of Bumpus et al. and Niu et al.; concretely they satisfy

    A[a,b] = A[a,p] ∩ A[p,b]                             (Lean: persistent_glue)
    C[a,b] = C[a,p] ∪ C[p,b],  C[a,p] ∩ C[p,b] = C[p,p]  (Lean: cumulative_union,
                                                             cumulative_inter_eq_point)

for `a ≤ p ≤ b`. Evaluate a narrative by calling it: `A(lo, hi)`, `A(t)`.
"""

abstract type AbstractNarrative end

"""
    persistent(program)

The persistent narrative: `A(lo, hi)` is the vector of atoms whose support
contains all of `[lo, hi]`; `A(t)` is the atoms active at `t`.
"""
struct PersistentNarrative <: AbstractNarrative
    program::Program
end
persistent(p::Program) = PersistentNarrative(p)

"""
    cumulative(program)

The cumulative narrative: `C(lo, hi)` is the vector of atoms whose support meets
`[lo, hi]`; `C(t)` is the atoms active at `t`.
"""
struct CumulativeNarrative <: AbstractNarrative
    program::Program
end
cumulative(p::Program) = CumulativeNarrative(p)

(n::PersistentNarrative)(lo, hi) = Atom[a for a in n.program.atoms if covers_closed(a.support, lo, hi)]
(n::CumulativeNarrative)(lo, hi) = Atom[a for a in n.program.atoms if meets_closed(a.support, lo, hi)]
(n::AbstractNarrative)(t) = n(t, t)

Base.show(io::IO, n::PersistentNarrative) = print(io, "persistent(", n.program, ")")
Base.show(io::IO, n::CumulativeNarrative) = print(io, "cumulative(", n.program, ")")
