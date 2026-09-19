# [Transport and stratification](@id howto-transport)

A program written for one model can move to another along a map of targets.

**Rename** targets with [`pushforward`](@ref):

```julia
q = pushforward(program, Dict(:beta => :inf))
```

If the map merges targets, new overlaps appear; scalings combine, absolute
assignments conflict, and the report says so.

**Stratify** an AlgebraicPetri model and **lift** the program with
[`stratify`](@ref) and [`lift`](@ref). The base net needs a reflexive
"stay" transition for every species that the strata net moves between:

```julia
types = LabelledPetriNet([:Pop], :infect => ((:Pop, :Pop) => (:Pop, :Pop)),
                         :disease => (:Pop => :Pop), :strata => (:Pop => :Pop))
sir = LabelledPetriNet([:S, :I, :R], :inf => ((:S, :I) => (:I, :I)), :rec => (:I => :R),
                       :stay_S => (:S => :S), :stay_I => (:I => :I), :stay_R => (:R => :R))
age = LabelledPetriNet([:young, :old],
                       :inf_yy => ((:young, :young) => (:young, :young)), :inf_yo => ((:young, :old) => (:young, :old)),
                       :inf_oy => ((:old, :young) => (:old, :young)),   :inf_oo => ((:old, :old) => (:old, :old)),
                       :dis_y => (:young => :young), :dis_o => (:old => :old), :ageing => (:young => :old))
st = stratify(sir, age, types,
              Dict(:inf => :infect, :rec => :disease, :stay_S => :strata, :stay_I => :strata, :stay_R => :strata),
              Dict(:inf_yy => :infect, :inf_yo => :infect, :inf_oy => :infect, :inf_oo => :infect,
                   :dis_y => :disease, :dis_o => :disease, :ageing => :strata))

stratified = Model(st.net)                 # species S_young, S_old, ...; rates inf_inf_yy, ...
lifted = lift(program, st.to_base)         # one copy of each atom per stratum
```

Catlab also exports a function named `lift`; if both packages are loaded
unqualified, write `lift_along` or `CategoricalInterventions.lift`.

A `Transfer` lifts within each stratum (`S_young → R_young`), read from the
tuple labels of the stratified net. Compose stratum-specific refinements as
usual:

```julia
school = Program(stratified, scale(:inf_inf_yy, 0.5; during=8..12, id=:school))
compose(lifted, school)
```

Pushing a stratified program forward along `st.to_base` merges the strata.
