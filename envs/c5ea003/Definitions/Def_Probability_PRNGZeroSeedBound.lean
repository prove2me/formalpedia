-- Prove2me | Definitions.Def_Probability_PRNGZeroSeedBound
-- name    : Probability_PRNGZeroSeedBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:22.87825+00:00
-- url     : https://prove2.me/theorems/1e143e0c-0ae1-4d06-b6b1-bc3c7300b001
-- title:
--   Aether Catalog definitions — Probability_PRNGZeroSeedBound
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PRNGZeroSeedBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PRNGZeroSeedBound.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_PRNGEnumerationL1

/-!
# An improved counting bound: the zero-seed collapse

The general rarity bound `card_lfsrWords_le` counts one file per (taps, seed)
pair, i.e. `q^{2L}` files of length `n`.  That count is never attained for
`L ≥ 1`, because the `q^L` pairs with zero seed all produce the *same* file, the
all-zero one (`lfsr_pref_zero`).  Removing this collapse gives

```
|lfsrWords K L n| ≤ q^{2L} - q^L + 1        (`card_lfsrWords_le_zero_seed`)
```

which is a strict improvement (`card_lfsrWords_lt_pow_two_L`) and is **exactly
attained at `L = 1`** (`card_lfsrWords_one_eq_zero_seed_bound`), where the
order-one enumeration `card_lfsrWords_one` gives `q² - q + 1`.  At `L = 2` over
`GF(2)` the bound gives `13` against the true value `11`
(`card_lfsrWords_two_two_four`), so the remaining slack is exactly the
higher-order degeneracy that conjecture C1 predicts.
-/

namespace Catalog.Probability.SeedRec

open Finset

variable {K : Type*} [CommRing K] [Fintype K] [DecidableEq K]

/-- The (taps, seed) pairs with zero seed: `q^L` of them, all producing the
all-zero file. -/
def zeroSeedPairs (K : Type*) [CommRing K] [Fintype K] [DecidableEq K] (L : ℕ) :
    Finset ((Fin L → K) × (Fin L → K)) :=
  Finset.univ.image fun c : Fin L → K => (c, fun _ => (0 : K))





end Catalog.Probability.SeedRec


