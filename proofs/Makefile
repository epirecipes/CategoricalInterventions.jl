.PHONY: build clean check

# Fetch the prebuilt Mathlib olean cache, then build the proof library.
build:
	lake exe cache get
	lake build

# Fail if any `sorry` remains in the development.
check:
	@if grep -rnw --include='*.lean' sorry CategoricalInterventionsProofs CategoricalInterventionsProofs.lean; then \
		echo "sorry found"; exit 1; else echo "no sorry"; fi

clean:
	rm -rf .lake lake-manifest.json
