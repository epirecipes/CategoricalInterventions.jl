# Property tests mirroring the Lean theorems (see docs/src/verified.md).

const LAW_TARGETS = [Target(:a), Target(:b), Target(:c)]

function random_atom(rng, alg_kind)
    t = rand(rng, LAW_TARGETS)
    lo = rand(rng, 0:20); hi = lo + rand(rng, 1:10)
    eff = alg_kind == :mult ? Scale(rand(rng, (0.5, 0.8, 1.25, 2.0))) :
          alg_kind == :add  ? Add(rand(rng, -3:3)) :
          alg_kind == :affine ? (rand(rng) < 0.2 ? SetValue(rand(rng, 1.0:5.0)) : Scale(rand(rng, (0.5, 2.0)))) :
          rand(rng) < 0.5 ? Scale(2.0) : Add(1)
    return Atom(Symbol(:x, rand(rng, 1:10^6)), t, Span(lo, hi), eff)
end

function law_space(alg_kind)
    sp = TargetSpace()
    alg = alg_kind == :mult ? Multiplicative() : alg_kind == :add ? Additive() :
          alg_kind == :affine ? Affine(Multiplicative()) : Reject()
    for t in LAW_TARGETS
        declare!(sp, t, alg)
    end
    return sp
end

random_program(rng, kind, n) = Program([random_atom(rng, kind) for _ in 1:n]; space=law_space(kind))

function schedule_values(p, baseline, times)
    apply(p, Dict(t.name => fill(baseline, length(times)) for t in LAW_TARGETS), times; check=false)
end

@testset "Laws" begin
    rng = MersenneTwister(2026)
    times = collect(0:31)
    for kind in (:mult, :add, :affine, :reject), _ in 1:40
        p = random_program(rng, kind, rand(rng, 0:4))
        q = random_program(rng, kind, rand(rng, 0:4))
        r = random_program(rng, kind, rand(rng, 0:3))
        # compose_assoc, compose_nil
        @test compose(compose(p, q; check=false), r; check=false) == compose(p, compose(q, r; check=false); check=false)
        @test compose(Program(; space=p.space), p; check=false) == p == compose(p, Program(; space=p.space); check=false)
        # conflictFree_of_pairwise: pairwise check agrees with pointwise fold definedness
        pointwise_ok = all(all(v !== nothing for v in values(active_effects(p, t; check=false))) for t in times)
        @test validate(p) == pointwise_ok
        # conflictFree_append_left/right
        pq = compose(p, q; check=false)
        validate(pq) && (@test validate(p) && validate(q))
        # epochs_refine: every epoch of p++q lies inside an epoch of p or misses all of them
        for e in epochs(pq; check=false)
            inside = [x for x in epochs(p; check=false) if overlaps(x.support, e.support)]
            @test isempty(inside) || (length(inside) == 1 && inside[1].support.lo <= e.support.lo && e.support.hi <= inside[1].support.hi)
        end
        # persistent_glue and cumulative gluing on random closed intervals
        A, C = persistent(p), cumulative(p)
        a = rand(rng, 0:30); pp = a + rand(rng, 0:3); b = pp + rand(rng, 0:3)
        @test Set(A(a, b)) == intersect(Set(A(a, pp)), Set(A(pp, b)))
        @test Set(C(a, b)) == union(Set(C(a, pp)), Set(C(pp, b)))
        @test intersect(Set(C(a, pp)), Set(C(pp, b))) == Set(C(pp, pp))
        @test Set(A(a, a)) == Set(active(p, a))
        if validate(pq) && kind != :reject
            base = 1.0
            # apply_local
            for t in times
                isempty(active(p, t)) && (@test all(schedule_values(p, base, times)[k.name][t + 1] == base for k in LAW_TARGETS))
            end
            # apply_comm: program order never matters under a PCM
            spq = schedule_values(pq, base, times)
            sp_ = schedule_values(p, base, times)
            sqp = schedule_values(compose(q, p), base, times)
            for k in LAW_TARGETS
                @test spq[k.name] ≈ sqp[k.name]
            end
            # apply_append: (p ++ q) acts as q after p (apply_append_affine: when q is purely relative)
            if kind != :affine || !any(a -> a.effect isa SetValue, q.atoms)
                after = apply(q, Dict(k.name => sp_[k.name] for k in LAW_TARGETS), times)
                for k in LAW_TARGETS
                    @test spq[k.name] ≈ after[k.name]
                end
            end
            # lower_eq_apply: holding the last event value reproduces the schedule
            baseline = Dict(k.name => base for k in LAW_TARGETS)
            tab = lower(p, baseline)
            for t in times, k in LAW_TARGETS
                @test hold_last(tab, baseline, t)[k.name] ≈ sp_[k.name][t + 1]
            end
            # apply_pullback / grid sampling: sample then apply == apply at grid values
            grid = 0.0:0.5:31.0
            g = Dict(k.name => fill(base, length(grid)) for k in LAW_TARGETS)
            direct = apply(p, g, collect(grid))
            sampled = apply(sample(p, grid), g, collect(1:length(grid)))
            for k in LAW_TARGETS
                @test direct[k.name] ≈ sampled[k.name]
            end
        end
    end
    # fold_perm: PCM folds are order independent
    for kind in (:mult, :add, :affine), _ in 1:30
        p = random_program(rng, kind, 4)
        validate(p) || continue
        perm = Program(shuffle(rng, p.atoms); space=p.space)
        for t in times
            @test active_effects(p, t) == active_effects(perm, t)
        end
    end
end
