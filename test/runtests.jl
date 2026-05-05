using Test
using AlgebraicPetri
using Catlab: nparts
using CategoricalInterventions
using DiffEqCallbacks
using LabelledArrays
using OrdinaryDiffEq

mutable struct FakeIntegrator
    u::Vector{Float64}
    p::Vector{Float64}
    t::Float64
end

@testset "CategoricalInterventions.jl" begin
    beta = Target(:beta; kind=Parameter, value_type=Float64)
    gamma = Target(:gamma; kind=Parameter, value_type=Float64)

    @testset "Intervals" begin
        a = Interval(10, 30)
        b = Interval(20, 40)
        @test CategoricalInterventions.overlaps(a, b)
        @test CategoricalInterventions.intersection(a, b) == Interval(20, 30)
        @test_throws ArgumentError Interval(2, 2)
        @test isempty(InterventionProgram().atoms)
    end

    @testset "Different-target overlaps epochize" begin
        school = InterventionAtom(:school_closure, beta, Interval(10, 30), Scale(0.6))
        isolation = InterventionAtom(:case_isolation, gamma, Interval(20, 40), SetValue(0.25))
        program = compose_interventions(InterventionProgram(school), InterventionProgram(isolation))

        epochs = epochize(program)
        @test getfield.(getfield.(epochs, :support), :start) == [10, 20, 30]
        @test getfield.(getfield.(epochs, :support), :stop) == [20, 30, 40]
        @test length(epochs[1].effects) == 1
        @test length(epochs[2].effects) == 2
        @test length(epochs[3].effects) == 1

        applied = apply_interventions(program, Dict(:beta => 0.30, :gamma => 0.10))
        @test applied[1].values[:beta] ≈ 0.18
        @test applied[1].values[:gamma] ≈ 0.10
        @test applied[2].values[:beta] ≈ 0.18
        @test applied[2].values[:gamma] ≈ 0.25
        @test applied[3].values[:beta] ≈ 0.30
        @test applied[3].values[:gamma] ≈ 0.25
    end

    @testset "Same-target disjoint intervals glue" begin
        a = InterventionAtom(:phase1, beta, Interval(1, 3), SetValue(0.2))
        b = InterventionAtom(:phase2, beta, Interval(5, 7), SetValue(0.1))
        program = compose_interventions(InterventionProgram(a), InterventionProgram(b))
        @test isempty(conflicts(program))
        @test length(epochize(program)) == 2
    end

    @testset "Same-target overlaps conflict by default" begin
        a = InterventionAtom(:closure, beta, Interval(10, 30), Scale(0.6))
        b = InterventionAtom(:mandate, beta, Interval(20, 40), Scale(0.8))
        program = InterventionProgram(a, b)
        @test length(conflicts(program)) == 1
        @test_throws InterventionConflictError compose_interventions(InterventionProgram(a), InterventionProgram(b))
    end

    @testset "Combination algebras permit overlap" begin
        beta_mult = Target(:beta; kind=Parameter, value_type=Float64, algebra=MultiplicativeAlgebra())
        a = InterventionAtom(:closure, beta_mult, Interval(10, 30), Scale(0.6))
        b = InterventionAtom(:mandate, beta_mult, Interval(20, 40), Scale(0.8))
        program = compose_interventions(InterventionProgram(a), InterventionProgram(b))
        epochs = epochize(program)
        @test length(epochs) == 3
        applied = apply_interventions(program, Dict(:beta => 0.30))
        @test applied[1].values[:beta] ≈ 0.18
        @test applied[2].values[:beta] ≈ 0.144
        @test applied[3].values[:beta] ≈ 0.24
    end

    @testset "Target identity and value types" begin
        maybe_beta = Target(:beta; kind=Parameter, value_type=Union{Missing,Float64})
        @test maybe_beta.value_type == Union{Missing,Float64}

        beta_float = Target(:beta; kind=Parameter, value_type=Float64)
        @test_throws ArgumentError InterventionAtom(:bad_set, beta_float, Interval(1, 2), SetValue("fast"))

        bad_map = InterventionAtom(:bad_map, beta_float, Interval(1, 2), MapEffect(x -> string(x)))
        @test_throws ArgumentError apply_interventions(InterventionProgram(bad_map), Dict(:beta => 0.30))

        parameter_x = Target(:x; kind=Parameter, value_type=Float64)
        state_x = Target(:x; kind=State, value_type=Float64, algebra=AdditiveAlgebra())
        program = InterventionProgram(
            InterventionAtom(:parameter_x, parameter_x, Interval(0, 2), SetValue(1.0)),
            InterventionAtom(:state_x, state_x, Interval(0, 2), Add(2.0)),
        )
        epoch = only(epochize(program))
        @test length(epoch.effects) == 2
        @test Set(getfield.(collect(keys(epoch.effects)), :kind)) == Set([Parameter, State])
        @test_throws ErrorException apply_interventions(program, Dict(:x => 0.0))
    end

    @testset "Discrete schedules" begin
        beta_mult = Target(:beta; kind=Parameter, value_type=Float64, algebra=MultiplicativeAlgebra())
        program = InterventionProgram(InterventionAtom(:closure, beta_mult, Interval(2, 5), Scale(0.5)))
        times = collect(0:5)
        baseline = Dict(:beta => fill(0.30, length(times)))
        output = apply_discrete(program, baseline, times)
        @test output[:beta] ≈ [0.30, 0.30, 0.15, 0.15, 0.15, 0.30]

        range_baseline = Dict(:beta => range(0.30, stop=0.30, length=length(times)))
        range_output = apply_discrete(program, range_baseline, times)
        @test range_output[:beta] isa Vector
        @test range_output[:beta] ≈ [0.30, 0.30, 0.15, 0.15, 0.15, 0.30]
    end

    @testset "Unicode operators" begin
        beta_mult = ℙ(:beta; value_type=Float64, algebra=MultiplicativeAlgebra())
        gamma_state = 𝕊("I"; value_type=Float64, algebra=AdditiveAlgebra())
        support = 𝕀(10, 30)
        later = 𝕀(20, 40)

        @test beta_mult == Target(:beta; kind=Parameter, value_type=Float64)
        @test gamma_state == Target(:I; kind=State, value_type=Float64)
        @test 10 ∈ support
        @test !(30 ∈ support)
        @test support ∩ later == Interval(20, 30)

        closure = ι(:closure, beta_mult, support, κ(0.6))
        importation = ι(:importation, gamma_state, 𝕀(20, 21), δ(5.0))
        program = Π(closure) ⊕ importation
        applied = program ⊙ Dict(:beta => 0.30, :I => 10.0)

        @test length(program) == 2
        @test applied[1].values[:beta] ≈ 0.18
        @test applied[2].values[:I] ≈ 15.0

        assignment = ι(:set_gamma, ℙ(:gamma), 𝕀(5, 8), ≜(0.25))
        @test (Π(assignment) ⊙ Dict(:gamma => 0.1))[1].values[:gamma] ≈ 0.25

        times = collect(0:5)
        baseline = Dict(:beta => fill(0.30, length(times)))
        discrete = Π(ι(:short_closure, beta_mult, 𝕀(2, 5), κ(0.5))) ⊙ (baseline, times)
        @test discrete[:beta] ≈ [0.30, 0.30, 0.15, 0.15, 0.15, 0.30]
    end

    @testset "Catlab structures" begin
        school = InterventionAtom(:school_closure, beta, Interval(10, 30), Scale(0.6))
        isolation = InterventionAtom(:case_isolation, gamma, Interval(20, 40), SetValue(0.25))
        program = InterventionProgram(school, isolation)
        epochs = epochize(program; check=false)

        f = epoch_finfunction([10, 15, 20, 35], epochs)
        @test collect(f) == [1, 1, 2, 3]

        acset = as_acset(program)
        @test nparts(acset, :Atom) == 2
        @test nparts(acset, :TargetObj) == 2
    end

    @testset "Callback lowering helpers" begin
        beta_mult = Target(:beta; kind=Parameter, value_type=Float64, algebra=MultiplicativeAlgebra())
        infectious = Target(:I; kind=State, value_type=Float64, algebra=AdditiveAlgebra())
        closure = InterventionAtom(:closure, beta_mult, Interval(10.0, 30.0), Scale(0.6))
        masks = InterventionAtom(:masks, beta_mult, Interval(20.0, 40.0), Scale(0.8))
        importation = InterventionAtom(:importation, infectious, Interval(20.0, 21.0), Add(5.0))
        program = compose_interventions(InterventionProgram(closure, masks, importation))
        indexing = PetriIndexing(
            parameters=Dict(:beta => 1, :gamma => 2),
            states=Dict(:S => 1, :I => 2, :R => 3),
        )

        @test callback_times(program) == [10.0, 20.0, 30.0, 40.0]
        parameter_effects = active_parameter_effects(program, 25.0)
        @test parameter_effects[beta_mult] isa Scale
        @test parameter_effects[beta_mult].factor ≈ 0.48
        @test state_pulses_at(program, 20.0)[infectious] isa Add

        integ = FakeIntegrator([90.0, 10.0, 0.0], [0.30, 0.10], 20.0)
        apply_to_integrator!(integ, program, indexing, integ.t; baseline_p=[0.30, 0.10])
        @test integ.p ≈ [0.144, 0.10]
        @test integ.u ≈ [90.0, 15.0, 0.0]

        integ.t = 30.0
        apply_to_integrator!(integ, program, indexing, integ.t; baseline_p=[0.30, 0.10])
        @test integ.p ≈ [0.24, 0.10]

        cb = to_callback(program, indexing; baseline_p=[0.30, 0.10])
        @test occursin("DiscreteCallback", string(typeof(cb)))
        @test occursin("PresetTimeFunction", string(typeof(cb)))

        state_program = InterventionProgram(importation)
        state_indexing = PetriIndexing(parameters=Dict{Symbol,Int}(), states=Dict(:S => 1, :I => 2, :R => 3))
        state_integ = FakeIntegrator([90.0, 10.0, 0.0], Float64[], 20.0)
        apply_to_integrator!(state_integ, state_program, state_indexing, state_integ.t)
        @test state_integ.u ≈ [90.0, 15.0, 0.0]

        state_cb = to_callback(state_program, state_indexing)
        @test occursin("DiscreteCallback", string(typeof(state_cb)))

        unrelated = FakeIntegrator([90.0, 10.0, 0.0], [0.30, 0.42], 20.0)
        apply_parameter_effects!(unrelated.p, InterventionProgram(closure), indexing, [0.30, 0.10], 20.0)
        @test unrelated.p ≈ [0.18, 0.42]
        apply_parameter_effects!(unrelated.p, InterventionProgram(closure), indexing, [0.30, 0.10], 30.0)
        @test unrelated.p ≈ [0.30, 0.42]

        mixed_indexing = PetriIndexing(parameters=[:inf, :rec], states=Dict(:S => 1, :I => 2, :R => 3))
        @test mixed_indexing.parameters[:inf] == :inf
        @test mixed_indexing.states[:S] == 1

        parameter_x = Target(:x; kind=Parameter, value_type=Float64, algebra=MultiplicativeAlgebra())
        state_x = Target(:x; kind=State, value_type=Float64, algebra=AdditiveAlgebra())
        same_name_program = InterventionProgram(
            InterventionAtom(:scale_x, parameter_x, Interval(0.0, 2.0), Scale(0.5)),
            InterventionAtom(:pulse_x, state_x, Interval(1.0, 2.0), Add(2.0)),
        )
        same_name_indexing = PetriIndexing(parameters=Dict(:x => 1), states=Dict(:x => 1))
        same_name_integ = FakeIntegrator([10.0], [4.0], 1.0)
        apply_to_integrator!(same_name_integ, same_name_program, same_name_indexing, 1.0; baseline_p=[4.0])
        @test same_name_integ.p ≈ [2.0]
        @test same_name_integ.u ≈ [12.0]
    end

    @testset "Callback baseline initialization and reuse" begin
        rate = Target(:rate; kind=Parameter, value_type=Float64, algebra=MultiplicativeAlgebra())
        program = InterventionProgram(
            InterventionAtom(:preexisting_reduction, rate, Interval(-1.0, 1.0), Scale(0.5)),
        )
        indexing = PetriIndexing(parameters=Dict(:rate => 1), states=Dict(:X => 1))
        cb = to_callback(program, indexing)

        function growth!(du, u, p, t)
            du[1] = p[1] * u[1]
            return nothing
        end

        prob1 = ODEProblem(growth!, [1.0], (0.0, 2.0), [2.0])
        sol1 = solve(prob1, Tsit5(); callback=cb, saveat=0.0:0.5:2.0, abstol=1e-9, reltol=1e-9)
        @test sol1.retcode == ReturnCode.Success
        @test sol1[1, end] ≈ exp(3.0) rtol=1e-5

        prob2 = ODEProblem(growth!, [1.0], (0.0, 2.0), [4.0])
        sol2 = solve(prob2, Tsit5(); callback=cb, saveat=0.0:0.5:2.0, abstol=1e-9, reltol=1e-9)
        @test sol2.retcode == ReturnCode.Success
        @test sol2[1, end] ≈ exp(6.0) rtol=1e-5
    end

    @testset "AlgebraicPetri SIR integration" begin
        sir_model = LabelledPetriNet(
            [:S, :I, :R],
            :inf => ((:S, :I) => (:I, :I)),
            :rec => (:I => :R),
        )
        u0 = LVector(S=990.0, I=10.0, R=0.0)
        p0 = LVector(inf=0.05 * 10.0 / sum(u0), rec=0.25)
        prob = ODEProblem(vectorfield(sir_model), u0, (0.0, 40.0), p0)

        baseline = solve(prob, Tsit5(); saveat=0.5)
        @test baseline.retcode == ReturnCode.Success

        inf_rate = Target(
            :inf;
            kind=Parameter,
            value_type=Float64,
            algebra=MultiplicativeAlgebra(),
        )
        susceptible = Target(:S; kind=State, value_type=Float64, algebra=AdditiveAlgebra())
        recovered = Target(:R; kind=State, value_type=Float64, algebra=AdditiveAlgebra())
        indexing = PetriIndexing(parameters=[:inf, :rec], states=[:S, :I, :R])

        lockdown = InterventionProgram(
            InterventionAtom(:lockdown, inf_rate, Interval(5.0, 25.0), Scale(0.5)),
        )
        lockdown_cb = to_callback(lockdown, indexing; baseline_p=p0)
        lockdown_sol = solve(prob, Tsit5(); callback=lockdown_cb, saveat=0.5)

        vaccination = InterventionProgram(
            InterventionAtom(:vaccinate_from_s, susceptible, Interval(15.0, 16.0), Add(-50.0)),
            InterventionAtom(:vaccinate_to_r, recovered, Interval(15.0, 16.0), Add(50.0)),
        )
        vaccination_cb = to_callback(vaccination, indexing)
        vaccination_sol = solve(prob, Tsit5(); callback=vaccination_cb, saveat=0.5)

        combined = compose_interventions(lockdown, vaccination)
        combined_cb = to_callback(combined, indexing; baseline_p=p0)
        combined_sol = solve(prob, Tsit5(); callback=combined_cb, saveat=0.5)

        @test lockdown_sol.retcode == ReturnCode.Success
        @test vaccination_sol.retcode == ReturnCode.Success
        @test combined_sol.retcode == ReturnCode.Success
        @test lockdown_sol[3, end] < baseline[3, end]
        @test vaccination_sol[1, end] > baseline[1, end]
        @test combined_sol[3, end] < baseline[3, end]
        @test sum(lockdown_sol.u[end]) ≈ sum(u0)
        @test sum(vaccination_sol.u[end]) ≈ sum(u0)
        @test sum(combined_sol.u[end]) ≈ sum(u0)
    end
end
