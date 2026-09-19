@testset "Narrative windows and truth values" begin
    sp = sir_space()
    p = @interventions sp begin
        a = scale(:beta, 0.5; during=0..21)
        b = scale(:beta, 0.5; during=21.5..40)
        c = set(:gamma, 0.2; during=12..38)
    end
    w = NarrativeWindow([Target(:beta), Target(:gamma)], 0:5:50)
    s = subobject(w, p)
    tv(j, k) = truth_value(s, Target(j), k)
    @test tv(:beta, 1) == :throughout
    @test tv(:beta, 4) == :throughout            # [15,20]: a ends at 21
    @test tv(:beta, 5) == :both_ends_not_throughout   # [20,25]: a ends at 21, b starts at 21.5
    @test tv(:beta, 9) == :false
    @test tv(:gamma, 3) == :end_only             # [10,15]: c starts at 12
    @test tv(:gamma, 8) == :start_only           # [35,40]: c ends at 38
    @test sometime(s, Target(:beta), 5) && !throughout(s, Target(:beta), 5)
    io = IOBuffer(); describe(s; io); @test occursin("lifted in between", String(take!(io)))

    # Heyting operations: P ⟹ Q is top where P is absent, and where Q holds
    q = subobject(w, Program(scale(:beta, 0.5; during=0..26); space=sp))
    imp = s ⟹ q
    @test truth_value(imp, Target(:beta), 1) == :throughout
    @test truth_value(imp, Target(:beta), 9) == :throughout
    @test truth_value(imp, Target(:beta), 7) == :false       # [30,35]: s holds, q does not
    @test truth_value(s ∧ q, Target(:beta), 3) == :throughout
    @test truth_value(s ∨ q, Target(:beta), 5) == :throughout
    @test truth_value(¬s, Target(:beta), 9) == :throughout
    @test (s ⟹ s) == subobject(w, Program([scale(:beta, 1; during=-1..100), scale(:gamma, 1; during=-1..100)]; space=sp))
end
