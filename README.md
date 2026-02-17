# What Bitcoin Can and Cannot Compute

A Lean 4 + Mathlib formalization of Bounded-Resource Automata (BRA) and their application to cryptocurrency ledger models.

## Results

- **Finiteness**: A value-only BRA with bound *C* has a finite state space of cardinality at most *(C+1)^C*, proved via injective histogram encoding (`state_space_finite`)
- **Infinite identity tracking**: An identity-tracking BRA (IT-BRA) has a countably infinite state space (`itstate_infinite`)
- **Petri net correspondence**: Value-only BRAs correspond to bounded Petri nets via a weighted place invariant *w(p) = p + 1* (`weighted_count_eq_sumValues`)
- **Collapse map**: A map from Bitcoin's UTXO model to Ethereum's account model that is surjective (`collapse_surjective`), not injective (`collapse_not_injective`), and not faithful (`collapse_not_faithful`)
- **Conservation commutes**: Total value is preserved by collapse (`conservation_commutes`)

882 lines of Lean 4. 74 declarations. Zero errors. Zero `sorry`s.

## Building

```bash
# Install Lean 4 via elan (if not already installed)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build the library
lake build
```

Building fetches Mathlib and compiles all 7 files (893 build jobs). First build takes several minutes due to Mathlib.

## Library Structure

| File | Lines | Declarations | Key theorem |
|------|------:|-------------:|-------------|
| `BRA/Basic.lean` | 139 | 13 | `State.apply` |
| `BRA/Finiteness.lean` | 98 | 9 | `state_space_finite` |
| `BRA/IdentityTracking.lean` | 166 | 8 | `itstate_infinite` |
| `BRA/PetriNet.lean` | 148 | 15 | `weighted_count_eq_sumValues` |
| `BRA/Separation.lean` | 61 | 5 | `bra_state_space_card_bound` |
| `Bitcoin/UTXO.lean` | 106 | 11 | `conservation_functor` |
| `Comparison/Collapse.lean` | 164 | 13 | `conservation_commutes` |

## Paper

The accompanying paper is in `paper/`. To compile:

```bash
cd paper
pdflatex main.tex && bibtex main && pdflatex main.tex && pdflatex main.tex
```

## Computational Verification

`scripts/bra_verify.py` provides computational checks on small instances:

```bash
python3 scripts/bra_verify.py
```

## Toolchain

- Lean 4.28.0-rc1
- Mathlib (pinned via `lake-manifest.json`)

## License

MIT
