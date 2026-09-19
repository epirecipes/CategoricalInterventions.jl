@testset "v0.1 names still work" begin
    beta = Target(:beta; kind=Parameter)
    a = InterventionAtom(:closure, beta, Interval(10, 30), Scale(0.6))
    b = InterventionAtom(:mandate, beta, Interval(20, 40), Scale(0.8))
    p = InterventionProgram(a, b)
    @test length(conflicts(p)) == 1
    @test_throws InterventionConflictError compose_interventions(InterventionProgram(a), InterventionProgram(b))
    sp = TargetSpace(); declare!(sp, :beta, Multiplicative(); value_type=Float64)
    ok = compose_interventions(InterventionProgram(a; space=sp), InterventionProgram(b; space=sp))
    @test length(epochize(ok)) == 3
    @test apply_interventions(ok, Dict(:beta => 0.3))[2].values[:beta] ≈ 0.144
    @test apply_discrete(InterventionProgram(InterventionAtom(:c, beta, Interval(2, 5), Scale(0.5)); space=sp),
                         Dict(:beta => fill(0.3, 6)), collect(0:5))[:beta] ≈ [0.3, 0.3, 0.15, 0.15, 0.15, 0.3]
    ix = PetriIndexing(parameters=[:inf, :rec], states=[:S, :I, :R])
    @test ix.parameters[:inf] == :inf
    @test callback_times(ok) == [10, 20, 30, 40]
end
