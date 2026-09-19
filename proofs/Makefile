.PHONY: build clean check

# Fetch the prebuilt Mathlib olean cache, then build the proof library.
build:
	lake exe cache get
	lake build

# Fail if any `sorry` remains in the development.
check:
	@! grep -rn "sorry" CategoricalInterventionsProofs CategoricalInterventionsProofs.lean

clean:
	rm -rf .lake lake-manifest.json
