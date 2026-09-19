@testset "Supports" begin
    a, b = Span(10, 30), Span(20, 40)
    @test overlaps(a, b) && intersection(a, b) == Span(20, 30)
    @test 10 ∈ a && !(30 ∈ a) && 15 ∈ (10 .. 30)
    @test_throws ArgumentError Span(2, 2)
    @test intersection(Span(0, 10), Instant(5)) == Instant(5)
    @test intersection(Span(0, 10), Instant(10)) === nothing
    @test CI.covers_closed(a, 10, 29) && !CI.covers_closed(a, 10, 30)
    @test CI.meets_closed(a, 30, 35) == false && CI.meets_closed(a, 29, 35)
    @test Interval(1, 2) == Span(1, 2)
    # support_ordConnected: supports are order-convex
    for s in (Span(3, 9), Instant(4)), x in 0:10, z in x:10, y in x:z
        (x ∈ s && z ∈ s) && @test y ∈ s
    end
end

@testset "Effects and algebras" begin
    @test apply_effect(Scale(0.5), 4.0) == 2.0
    @test apply_effect(AffineEffect(SetValue(2.0), Scale(3.0)), 100.0) == 6.0
    @test combine(Multiplicative(), Scale(0.5), Scale(0.4)) == Scale(0.2)
    @test combine(Additive(), Add(1), Transfer(:R, 3)) == Add(-2)
    @test combine(Cap(), CapAt(5), CapAt(3)) == CapAt(3)
    @test combine(Reject(), Scale(1), Scale(2)) === nothing
    @test combine(Reject(), Identity(), Scale(2)) == Scale(2)
    aff = Affine(Multiplicative())
    @test combine(aff, SetValue(2.0), Scale(3.0)) == AffineEffect(SetValue(2.0), Scale(3.0))
    @test combine(aff, Scale(3.0), SetValue(2.0)) == AffineEffect(SetValue(2.0), Scale(3.0))
    @test combine(aff, SetValue(1.0), SetValue(2.0)) === nothing
    @test combine(aff, Scale(2.0), Add(1.0)) === nothing
    @test CI.required_algebra(Scale(1), Scale(2)) == Multiplicative()
    @test CI.required_algebra(SetValue(1), Scale(2)) == Affine(Multiplicative())
end

@testset "Atoms and well-formedness" begin
    @test_throws ArgumentError Atom(:x, Target(:beta), Instant(1), Scale(2))
    @test_throws ArgumentError Atom(:x, Target(:S, State), Span(1, 2), Add(1))
    @test_throws ArgumentError Atom(:x, Target(:beta), Span(1, 2), Transfer(:R, 1))
    a = Atom(:x, Target(:S, State), Span(1, 2), Flow(:R, 0.1))
    @test isempty(expand(a))
    t = Atom(:v, Target(:S, State), Instant(3), Transfer(:R, 5))
    @test expand(t) == [Target(:S, State) => Transfer(:R, 5), Target(:R, State) => Add(5)]
    old = InterventionAtom(:old, Target(:S, State), Span(15.0, 16.0), Add(1.0))
    @test old.support == Instant(15.0)
end

@testset "DSL and @interventions" begin
    sp = sir_space()
    prog = @interventions sp begin
        closure = scale(:beta, 0.6; during=10..30)
        isolate = set(:gamma, 0.25; during=20..40)
        vax     = transfer(:S => :R, 50; at=15)
        seed    = add(:I, 5; at=20)
    end
    @test length(prog) == 4 && prog[1].id == :closure && prog[3].effect == Transfer(:R, 50)
    @test prog[1].target == Target(:beta) && prog[4].target == Target(:I, State)
    @test_throws ArgumentError scale(:beta, 0.5)
    @test_throws ArgumentError scale(:beta, 0.5; during=1..2, at=1)
    @test cap(:c, 5; during=(0, 1)).effect == CapAt(5)
    @test floor_at(:c, 5; during=0:1).support == Span(0, 1)
    @test custom(:beta, x -> x^2; during=0..1, label=:square).effect.label == :square
    @test flow(:S => :R; rate=0.1, during=0..5).effect == Flow(:R, 0.1)
end

@testset "Conflicts, composition, epochs" begin
    sp = sir_space()
    closure = scale(:beta, 0.6; during=10..30, id=:closure)
    masks = scale(:beta, 0.8; during=20..40, id=:masks)
    isolate = set(:gamma, 0.25; during=20..40, id=:isolate)
    p = Program([closure, masks, isolate]; space=sp)
    @test validate(p)
    es = epochs(p)
    @test [e.support for e in es] == [Span(10, 20), Span(20, 30), Span(30, 40)]
    @test apply_effect(es[2].effects[Target(:beta)], 1.0) ≈ 0.48
    vals = apply(p, Dict(:beta => 0.3, :gamma => 0.1))
    @test vals[2].values[:beta] ≈ 0.144 && vals[3].values[:gamma] ≈ 0.25 && vals[1].values[:gamma] ≈ 0.1

    # set-then-scale is not a conflict; two sets are
    q = compose(p, Program(set(:beta, 0.1; during=15..35, id=:absolute); space=sp))
    @test apply(q, Dict(:beta => 0.3, :gamma => 0.1))[3].values[:beta] ≈ 0.1 * 0.48   # [20,30): set, then both scalings
    r = Program([set(:beta, 0.1; during=0..10, id=:a), set(:beta, 0.2; during=5..15, id=:b)]; space=sp)
    cs = conflicts(r)
    @test length(cs) == 1 && cs[1].left.id == :a && cs[1].right.id == :b && cs[1].overlap == Span(5, 10)
    @test cs[1].required == LatestWins()
    @test_throws InterventionConflictError compose(Program(r[1]; space=sp), Program(r[2]; space=sp))
    @test_throws InterventionConflictError epochs(r)
    lax = epochs(r; check=false)
    @test lax[2].effects[Target(:beta)] === nothing
    io = IOBuffer(); explain(r; io); @test occursin("conflict", String(take!(io)))

    # default Reject on undeclared targets
    u = Program([scale(:x, 2; during=0..2, id=:u1), scale(:x, 3; during=1..3, id=:u2)])
    @test length(conflicts(u)) == 1 && conflicts(u)[1].required == Multiplicative()
    # different targets never conflict; disjoint same-target never conflict
    @test validate(Program([scale(:x, 2; during=0..2), scale(:y, 3; during=0..2)]))
    @test validate(Program([scale(:x, 2; during=0..2), scale(:x, 3; during=2..4)]))

    # ordered policies
    sp2 = TargetSpace(); declare!(sp2, :beta, LatestWins())
    lw = Program([set(:beta, 0.2; during=0..10, id=:a), set(:beta, 0.1; during=5..15, id=:b)]; space=sp2)
    @test validate(lw) && apply(lw, Dict(:beta => 1.0))[2].values[:beta] == 0.1
    sp3 = TargetSpace(); declare!(sp3, :beta, HighestPriority())
    hp = Program([set(:beta, 0.2; during=0..10, id=:a, metadata=Dict(:priority => 5)),
                  set(:beta, 0.1; during=5..15, id=:b)]; space=sp3)
    @test apply(hp, Dict(:beta => 1.0))[2].values[:beta] == 0.2

    # merging spaces that disagree is an error
    sp4 = TargetSpace(); declare!(sp4, :beta, Multiplicative())
    @test_throws ErrorException compose(Program(closure; space=sp), Program(masks; space=sp4))

    # restrict
    rs = restrict(p, 15, 25)
    @test [a.support for a in rs.atoms] == [Span(15, 25), Span(20, 25), Span(20, 25)]
    @test table(p)[1].target == :beta
end

@testset "Value types" begin
    sp = TargetSpace(); declare!(sp, :beta, Reject(); value_type=Float64)
    p = Program(set(:beta, "fast"; during=1..2); space=sp)
    @test_throws ArgumentError apply(p, Dict(:beta => 0.3))
    m = Program(custom(:beta, x -> string(x); during=1..2); space=sp)
    @test_throws ArgumentError apply(m, Dict(:beta => 0.3))
    ok = Program(custom(:beta, x -> 2x; during=1..2); space=sp)
    @test apply(ok, Dict(:beta => 0.3))[1].values[:beta] ≈ 0.6
    mixed = Program([set(:x, 1.0; during=0..2), add(:x, 2.0; at=1)])
    @test_throws ErrorException apply(mixed, Dict(:x => 0.0))
end

@testset "Narratives" begin
    sp = sir_space()
    p = @interventions sp begin
        a = scale(:beta, 0.5; during=0..20)
        b = scale(:beta, 0.5; during=20.5..40)
        v = transfer(:S => :R, 1; at=10)
    end
    A, C = persistent(p), cumulative(p)
    ids(x) = Set(getfield.(x, :id))
    @test ids(A(0, 19)) == Set([:a]) && ids(A(0, 20)) == Set() && ids(A(10)) == Set([:a, :v])
    @test ids(C(19, 21)) == Set([:a, :b]) && ids(C(20, 20.4)) == Set()
    @test throughout(p, :beta, (5, 15)) && !throughout(p, :beta, (15, 25)) && sometime(p, :beta, (15, 25))
end

@testset "Schedules, sampling, lowering" begin
    sp = sir_space()
    p = @interventions sp begin
        closure = scale(:beta, 0.5; during=2..5)
        seed    = add(:I, 5.0; at=3)
    end
    times = collect(0:6)
    base = Dict(:beta => fill(0.30, 7), :I => zeros(7))
    out = apply(p, base, times)
    @test out[:beta] ≈ [0.30, 0.30, 0.15, 0.15, 0.15, 0.30, 0.30]
    @test out[:I] == [0, 0, 0, 5.0, 0, 0, 0]
    rng = Dict(:beta => range(0.3, 0.3; length=7), :I => zeros(7))
    @test apply(p, rng, times)[:beta] isa Vector
    @test apply(p, Dict(:beta => fill(0.3, 7)), times)[:beta] ≈ out[:beta]   # pulses on absent states ignored

    grid = 0.0:0.5:6.0
    s = sample(p, grid)
    @test s[1].support == Span(5, 11) && s[2].support == Instant(7)
    b2 = Dict(:beta => fill(0.3, length(grid)))
    @test apply(p, b2, collect(grid))[:beta] == apply(s, b2, collect(1:length(grid)))[:beta]

    tab = lower(p, Dict(:beta => 0.3))
    @test first.(tab) == [2, 3, 5]
    @test hold_last(tab, Dict(:beta => 0.3), 4)[:beta] ≈ 0.15 && hold_last(tab, Dict(:beta => 0.3), 1)[:beta] ≈ 0.3
    @test event_times(p) == [2, 3, 5]
    @test active_parameter_effects(p, 2.5)[Target(:beta)] == Scale(0.5)
    @test state_pulses_at(p, 3)[Target(:I, State)] == Add(5.0)
end

@testset "Transport" begin
    sp = sir_space()
    p = @interventions sp begin
        closure = scale(:beta, 0.6; during=10..30)
        vax     = transfer(:S => :R, 50; at=15)
    end
    f = Dict(:beta => :beta_y, :S => :S_y, :R => :R_y)
    q = pushforward(p, f)
    @test q[1].target == Target(:beta_y) && q[2].effect == Transfer(:R_y, 50) && algebra(q, Target(:beta_y)) == Affine(Multiplicative())
    g = Dict(:beta_y => :b)
    @test pushforward(pushforward(p, f), g) == pushforward(p, t -> CI._target_map(g)(CI._target_map(f)(t)))
    # merging targets creates a conflict
    two = Program([scale(:beta, 0.5; during=0..10, id=:x), scale(:gamma, 0.5; during=0..10, id=:y)])
    @test_throws InterventionConflictError pushforward(two, Dict(:gamma => :beta))
    @test length(conflicts(pushforward(two, Dict(:gamma => :beta); check=false))) == 1

    π = Dict(:beta_y => :beta, :beta_o => :beta, :S_y => :S, :S_o => :S, :R_y => :R, :R_o => :R)
    strata = Dict(Target(:S_y, State) => :y, Target(:S_o, State) => :o, Target(:R_y, State) => :y, Target(:R_o, State) => :o)
    L = lift(p, π; strata)
    @test length(L) == 4 && Set(a.target.name for a in L.atoms) == Set([:beta_y, :beta_o, :S_y, :S_o])
    @test [a.effect for a in L.atoms if a.target.name == :S_y] == [Transfer(:R_y, 50)]
    @test validate(L)
    @test_throws ErrorException lift(p, π)   # transfer needs strata
    # conflict-free iff
    bad = Program([scale(:beta, 0.5; during=0..10, id=:x), set(:beta, 0.5; during=0..10, id=:y), set(:beta, 0.1; during=5..8, id=:z)]; space=sp)
    @test !validate(bad) && !validate(lift(bad, Dict(:beta_y => :beta, :beta_o => :beta); check=false))
    # composing a stratum-specific refinement
    L2 = compose(L, Program(scale(:beta_y, 0.5; during=12..14, id=:school); space=L.space))
    @test apply(L2, Dict(:beta_y => 1.0, :beta_o => 1.0))[2].values[:beta_y] ≈ 0.3
end

@testset "Inference" begin
    sp = sir_space()
    p = @interventions sp begin
        a = scale(:beta, 0.6; during=10.0..30.0)
        b = scale(:beta, 0.8; during=20.0..40.0)
        c = add(:gamma, 0.1; during=5.0..15.0)
    end
    declare!(sp, :gamma, Affine(Additive()); value_type=Float64)
    times = collect(0.0:1.0:50.0)
    base = Dict(:beta => fill(0.3, 51), :gamma => fill(0.1, 51))
    obs = apply(p, base, times)
    inf = infer(base, Dict(:beta => obs[:beta], :gamma => obs[:gamma]), times; space=sp)
    @test apply(inf, base, times)[:beta] ≈ obs[:beta] && apply(inf, base, times)[:gamma] ≈ obs[:gamma]
    @test Set((a.target.name, a.support, a.effect) for a in inf.atoms) ==
          Set([(:beta, Span(10.0, 20.0), Scale(0.6)), (:beta, Span(20.0, 30.0), Scale(0.6 * 0.8)),
               (:beta, Span(30.0, 40.0), Scale(0.8)), (:gamma, Span(5.0, 15.0), Add(0.1))])
end

@testset "Unicode" begin
    β = ℙ(:beta); I = 𝕊("I")
    @test β == Target(:beta) && I == Target(:I, State)
    @test 10 ∈ 𝕀(10, 30) && 𝕀(10, 30) ∩ 𝕀(20, 40) == Span(20, 30)
    sp = sir_space()
    prog = Π(ι(:closure, β, 𝕀(10, 30), κ(0.6)); space=sp) ⊕ ι(:seed, I, 𝕀(20, 21), δ(5.0))
    @test length(prog) == 2 && prog[2].support == Instant(20)
    @test (prog ⊙ Dict(:beta => 0.3))[1].values[:beta] ≈ 0.18
    @test (Π(ι(:g, ℙ(:gamma), 𝕀(5, 8), ≜(0.25))) ⊙ Dict(:gamma => 0.1))[1].values[:gamma] ≈ 0.25
    @test (Π(ι(:c, β, 𝕀(2, 5), κ(0.5))) ⊙ (Dict(:beta => fill(0.3, 6)), collect(0:5)))[:beta] ≈ [0.3, 0.3, 0.15, 0.15, 0.15, 0.3]
end
