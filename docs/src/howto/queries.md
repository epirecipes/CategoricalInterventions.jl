# [Temporal queries](@id howto-queries)

Ask whether a target is under intervention over a window:

```julia
throughout(program, :inf, (20, 30))   # some atom on :inf covers all of [20, 30]
sometime(program, :inf, (20, 30))     # some atom on :inf meets [20, 30]
```

These evaluate the persistent and cumulative narratives, `persistent(program)`
and `cumulative(program)`, which can also be called directly on `(lo, hi)`.

For the logic of the paper by Niu et al., build a window on a grid and take
the program's subobject:

```julia
w = NarrativeWindow([Target(:inf), Target(:rec)], 0:5:50)
s = subobject(w, program)
describe(s)                       # one of five truth values per unit interval
truth_value(s, Target(:inf), 4)   # :throughout, :start_only, :end_only,
                                  # :both_ends_not_throughout, or :false
```

Subobjects of one window form a Heyting algebra:

```julia
q = subobject(w, other_program)
s ⟹ q      # wherever s is in force, is q?
s ∧ q; s ∨ q; ¬s
```

Subobjects are compared target by target, so `s ⟹ q` relates the two
programs on each shared target. To ask whether one policy implies another
when they touch different targets, first `pushforward` both onto a common
target name.

Queries act on the program as specified, on a finite window, not on
simulation output.
