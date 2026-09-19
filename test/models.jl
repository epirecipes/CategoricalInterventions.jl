using Catlab.CategoricalAlgebra: ACSetTransformation, dom

@testset "Models and lowering" begin
    m = Model(nothing; parameters=[:beta, :gamma], states=Dict(:S => 1, :I => 2, :R => 3),
              invariants=[Conserved([:S, :I, :R]), Nonnegative([:S])])
    @test algebra(m.space, Target(:beta)) == Affine(Multiplicative()) && algebra(m.space, Target(:I, State)) == Additive()
    @test Set(parameters(m)) == Set([:beta, :gamma]) && Set(states(m)) == Set([:S, :I, :R])
    prog = @interventions m begin
        closure = scale(:beta, 0.6; during=10.0..30.0)
        masks   = scale(:beta, 0.8; during=20.0..40.0)
        seed    = add(:I, 5.0; at=20.0)
        vax     = transfer(:S => :R, 10.0; at=20.0)
    end
    @test check_targets(prog, m) === prog
    @test_throws ErrorException check_targets(Program(m, scale(:zeta, 1; during=0..1)), m)

    ix = Indexing(parameters=Dict(:beta => 1, :gamma => 2), states=Dict(:S => 1, :I => 2, :R => 3))
    integ = FakeIntegrator([90.0, 10.0, 0.0], [0.30, 0.10], 20.0)
    apply_to_integrator!(integ, prog, ix, integ.t; baseline_p=[0.30, 0.10])
    @test integ.p ≈ [0.144, 0.10] && integ.u ≈ [80.0, 15.0, 10.0]
    integ.t = 30.0
    apply_to_integrator!(integ, prog, ix, integ.t; baseline_p=[0.30, 0.10])
    @test integ.p ≈ [0.24, 0.10]
    unrelated = FakeIntegrator([90.0, 10.0, 0.0], [0.30, 0.42], 20.0)
    apply_parameter_effects!(unrelated.p, Program(prog[1]; space=m.space), ix, [0.30, 0.10], 20.0)
    @test unrelated.p ≈ [0.18, 0.42]

    # invariants
    viol = Program(m, add(:S, -1000.0; at=1.0))
    u = [90.0, 10.0, 0.0]
    @test_throws InvariantViolation apply_state_pulses!(u, viol, m, 1.0)
    ok = Program(m, transfer(:S => :R, 90.0; at=1.0))
    @test apply_state_pulses!([90.0, 10.0, 0.0], ok, m, 1.0) ≈ [0.0, 10.0, 90.0]
    neg = Program(m, transfer(:S => :R, 95.0; at=1.0))
    @test_throws InvariantViolation apply_state_pulses!([90.0, 10.0, 0.0], neg, m, 1.0)

    # mixed labelled and positional selectors; same name as parameter and state
    mixed = Indexing(parameters=[:inf, :rec], states=Dict(:S => 1, :I => 2, :R => 3))
    @test mixed.parameters[:inf] == :inf && mixed.states[:S] == 1
    sp = TargetSpace(); declare!(sp, :x, Multiplicative()); declare!(sp, :x, Additive(); kind=State)
    same = Program([scale(:x, 0.5; during=0.0..2.0), add(:x, 2.0; at=1.0)]; space=sp)
    ix2 = Indexing(parameters=Dict(:x => 1), states=Dict(:x => 1))
    it = FakeIntegrator([10.0], [4.0], 1.0)
    apply_to_integrator!(it, same, ix2, 1.0; baseline_p=[4.0])
    @test it.p ≈ [2.0] && it.u ≈ [12.0]
end

@testset "Flows on function models" begin
    sir_ode!(du, u, p, t) = (du[1] = -p[1] * u[1] * u[2]; du[2] = p[1] * u[1] * u[2] - p[2] * u[2]; du[3] = p[2] * u[2]; nothing)
    m = Model(sir_ode!; parameters=Dict(:inf => 1, :rec => 2), states=Dict(:S => 1, :I => 2, :R => 3),
              invariants=[Conserved([:S, :I, :R])])
    camp = Program(m, flow(:S => :R; rate=0.02, during=10.0..30.0, id=:campaign))
    aug = augment(m, camp)
    @test aug.model.indexing.parameters[:flow_S_R_campaign] == 3 && aug.extend([0.0005, 0.25]) == [0.0005, 0.25, 0.0]
    @test aug.program[1].effect == SetValue(0.02) && aug.program[1].target.name == :flow_S_R_campaign
    u0 = [990.0, 10.0, 0.0]; p0 = [0.0005, 0.25]; tspan = (0.0, 40.0)
    base = simulate(m, Program(m); u0, p0, tspan, alg=Tsit5(), saveat=0.5)
    fl = simulate(m, camp; u0, p0, tspan, alg=Tsit5(), saveat=0.5)
    @test fl[3, end] > base[3, end] && sum(fl.u[end]) ≈ 1000.0
    # the same flow on a labelled, out-of-place model agrees with the Petri-net augmentation
    sir_oop(u, p, t) = LVector(S=-p.inf * u.S * u.I, I=p.inf * u.S * u.I - p.rec * u.I, R=p.rec * u.I)
    ml = Model(sir_oop; parameters=[:inf, :rec], states=[:S, :I, :R])
    campl = Program(ml, flow(:S => :R; rate=0.02, during=10.0..30.0, id=:campaign))
    u0l = LVector(S=990.0, I=10.0, R=0.0); p0l = LVector(inf=0.0005, rec=0.25)
    fll = simulate(ml, campl; u0=u0l, p0=p0l, tspan, alg=Tsit5(), saveat=0.5, abstol=1e-10, reltol=1e-10)
    sir = LabelledPetriNet([:S, :I, :R], :inf => ((:S, :I) => (:I, :I)), :rec => (:I => :R))
    mp = Model(sir)
    flp = simulate(mp, Program(mp, campl.atoms); u0=u0l, p0=p0l, tspan, alg=Tsit5(), saveat=0.5, abstol=1e-10, reltol=1e-10)
    @test maximum(abs, Array(fll) .- Array(flp)) < 1e-6
    # discrete models: the flow moves a per-step fraction, and pulses apply before the update
    double!(du, u, p, t) = (du[1] = 2u[1]; nothing)
    md = Model(double!; parameters=Dict{Symbol,Int}(), states=Dict(:X => 1), kind=:discrete)
    sol = simulate(md, Program(md, add(:X, 10.0; at=2.0)); u0=[1.0], p0=Float64[], tspan=(0.0, 4.0), alg=FunctionMap(), dt=1.0)
    at(t) = sol.u[findlast(==(t), sol.t)][1]
    @test at(2.0) == 14.0 && at(3.0) == 28.0 && at(4.0) == 56.0   # u(2) = 4 + 10 before the update to step 3
end

@testset "Callback: baseline capture and reuse" begin
    m = Model(nothing; parameters=Dict(:rate => 1), states=Dict(:X => 1))
    prog = Program(m, scale(:rate, 0.5; during=-1.0..1.0, id=:pre))
    cb = to_callback(prog, m)
    growth!(du, u, p, t) = (du[1] = p[1] * u[1]; nothing)
    sol1 = solve(ODEProblem(growth!, [1.0], (0.0, 2.0), [2.0]), Tsit5(); callback=cb, abstol=1e-9, reltol=1e-9)
    @test sol1[1, end] ≈ exp(3.0) rtol = 1e-5
    sol2 = solve(ODEProblem(growth!, [1.0], (0.0, 2.0), [4.0]), Tsit5(); callback=cb, abstol=1e-9, reltol=1e-9)
    @test sol2[1, end] ≈ exp(6.0) rtol = 1e-5
    @test occursin("DiscreteCallback", string(typeof(cb)))
end

@testset "AlgebraicPetri SIR" begin
    sir = LabelledPetriNet([:S, :I, :R], :inf => ((:S, :I) => (:I, :I)), :rec => (:I => :R))
    m = Model(sir)
    @test m.invariants == [Conserved([:S, :I, :R])] && algebra(m.space, Target(:inf)) == Affine(Multiplicative())
    u0 = LVector(S=990.0, I=10.0, R=0.0)
    p0 = LVector(inf=0.05 * 10.0 / sum(u0), rec=0.25)
    tspan = (0.0, 40.0)
    prog = @interventions m begin
        lockdown = scale(:inf, 0.5; during=5.0..25.0)
        vax      = transfer(:S => :R, 50.0; at=15.0)
    end
    base = simulate(m, Program(m); u0, p0, tspan, alg=Tsit5(), saveat=0.5)
    lock = simulate(m, Program(m, prog[1]); u0, p0, tspan, alg=Tsit5(), saveat=0.5)
    vax = simulate(m, Program(m, prog[2]); u0, p0, tspan, alg=Tsit5(), saveat=0.5)
    both = simulate(m, prog; u0, p0, tspan, alg=Tsit5(), saveat=0.5)
    @test all(s.retcode == ReturnCode.Success for s in (base, lock, vax, both))
    @test lock[3, end] < base[3, end] && vax[1, end] > base[1, end] && both[3, end] < base[3, end]
    @test all(sum(s.u[end]) ≈ sum(u0) for s in (lock, vax, both))

    # cross-check against the direct equations: same program, same numbers (naturality)
    sir_ode(u, p, t) = LVector(S=-p.inf * u.S * u.I, I=p.inf * u.S * u.I - p.rec * u.I, R=p.rec * u.I)
    ref = solve(ODEProblem(sir_ode, u0, tspan, p0), Tsit5(); callback=to_callback(prog, m; baseline_p=p0), saveat=0.5)
    @test maximum(abs, Array(both) .- Array(ref)) < 1e-6

    # flows by augmentation: a Petri-net morphism adds one transition
    camp = Program(m, flow(:S => :R; rate=0.02, during=10.0..30.0, id=:campaign))
    aug = augment(m, camp)
    @test nt(aug.model.metadata[:petri]) == 3 && aug.program[1].target.name == :flow_S_R_campaign
    @test aug.extend(p0).flow_S_R_campaign == 0.0
    @test_throws ErrorException to_callback(camp, m)
    fl = simulate(m, camp; u0, p0, tspan, alg=Tsit5(), saveat=0.5)
    @test fl[3, end] > base[3, end] && sum(fl.u[end]) ≈ sum(u0)
    # outside the span the augmented model equals the original (augment_restrict)
    early = simulate(m, camp; u0, p0, tspan=(0.0, 10.0), alg=Tsit5(), saveat=0.5)
    early_base = simulate(m, Program(m); u0, p0, tspan=(0.0, 10.0), alg=Tsit5(), saveat=0.5)
    g = 0.0:0.5:10.0
    @test maximum(abs, Array(early(g)) .- Array(early_base(g))) < 1e-8

    # transport along a Petri-net morphism: define once on SIR, lift to an age-stratified SIR
    types = LabelledPetriNet([:Pop], :infect => ((:Pop, :Pop) => (:Pop, :Pop)), :disease => (:Pop => :Pop), :strata => (:Pop => :Pop))
    sir_r = LabelledPetriNet([:S, :I, :R], :inf => ((:S, :I) => (:I, :I)), :rec => (:I => :R),
                             :stay_S => (:S => :S), :stay_I => (:I => :I), :stay_R => (:R => :R))
    age = LabelledPetriNet([:young, :old], :inf_yy => ((:young, :young) => (:young, :young)),
                           :inf_yo => ((:young, :old) => (:young, :old)), :inf_oy => ((:old, :young) => (:old, :young)),
                           :inf_oo => ((:old, :old) => (:old, :old)), :dis_y => (:young => :young), :dis_o => (:old => :old),
                           :ageing => (:young => :old))
    st = stratify(sir_r, age, types,
                  Dict(:inf => :infect, :rec => :disease, :stay_S => :strata, :stay_I => :strata, :stay_R => :strata),
                  Dict(:inf_yy => :infect, :inf_yo => :infect, :inf_oy => :infect, :inf_oo => :infect,
                       :dis_y => :disease, :dis_o => :disease, :ageing => :strata))
    strat, proj = st.net, st.to_base
    @test ns(strat) == 6 && nt(strat) == 9
    ms = Model(strat)
    @test Set(states(ms)) == Set([:S_young, :S_old, :I_young, :I_old, :R_young, :R_old])
    prog_r = Program(Model(sir_r), prog.atoms)
    lifted = lift(prog_r, proj)
    @test length(lifted) == 4 + 2 && validate(lifted)     # lockdown on 4 infection transitions, vax on 2 strata
    @test Set(a.target.name for a in lifted.atoms if a.effect isa Scale) == Set([:inf_inf_yy, :inf_inf_yo, :inf_inf_oy, :inf_inf_oo])
    @test [a.effect.to for a in lifted.atoms if a.effect isa Transfer && a.target.name == :S_young] == [:R_young]
    @test check_targets(lifted, ms) === lifted
    u0s = LVector(S_young=600.0, S_old=390.0, I_young=5.0, I_old=5.0, R_young=0.0, R_old=0.0)
    p0s = LVector(; (t => (startswith(string(t), "inf") ? 0.0005 : startswith(string(t), "rec") ? 0.25 : 0.0) for t in parameters(ms))...)
    sol = simulate(ms, lifted; u0=u0s, p0=p0s, tspan, alg=Tsit5(), saveat=0.5)
    @test sol.retcode == ReturnCode.Success && sum(sol.u[end]) ≈ sum(u0s)
    # with all strata symmetric and no ageing, the lifted program reproduces the base model exactly
    u0h = LVector(S_young=495.0, S_old=495.0, I_young=5.0, I_old=5.0, R_young=0.0, R_old=0.0)
    p0h = LVector(; (t => (startswith(string(t), "inf") ? p0.inf : startswith(string(t), "rec") ? p0.rec : 0.0) for t in parameters(ms))...)
    half = Program(Model(sir_r), scale(:inf, 0.5; during=5.0..25.0, id=:lockdown), transfer(:S => :R, 25.0; at=15.0, id=:vax))
    tight = (abstol=1e-10, reltol=1e-10)
    solh = simulate(ms, lift(half, proj); u0=u0h, p0=p0h, tspan, alg=Tsit5(), saveat=0.5, tight...)
    both_tight = simulate(m, prog; u0, p0, tspan, alg=Tsit5(), saveat=0.5, tight...)
    @test maximum(abs, (Array(solh)[1, :] .+ Array(solh)[2, :]) .- Array(both_tight)[1, :]) < 1e-5
    # a refinement on one stratum composes with the lifted program
    school = Program(ms, scale(:inf_inf_yy, 0.5; during=8.0..12.0, id=:school))
    @test validate(compose(lifted, school))
    # pushforward along the projection merges strata and can conflict
    young_only = Program(ms, scale(:inf_inf_yy, 0.5; during=0.0..10.0, id=:school2), scale(:inf_inf_oo, 0.5; during=0.0..10.0, id=:care))
    @test validate(pushforward(young_only, proj))    # scalings combine after merging
    sets = Program(ms, set(:inf_inf_yy, 0.1; during=0.0..10.0, id=:a), set(:inf_inf_oo, 0.2; during=0.0..10.0, id=:b))
    @test_throws InterventionConflictError pushforward(sets, proj)
end
