-- Prove2me | Theorems.Thm_Catalog_Probability_SeedRec_card_lfsrWords_le_zero_seed
-- name    : Catalog.Probability.SeedRec.card_lfsrWords_le_zero_seed
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:10:54.498351+00:00
-- url     : https://prove2.me/theorems/703b056f-6b01-4d1c-9284-88a86e42d171
-- title:
--   Improved rarity bound.
-- statement:
--   **Improved rarity bound.**  At most `q^{2L} - q^L + 1` files of length `n`
--   have linear complexity `≤ L`: the `q^L` zero-seed generators are all wasted on a
--   single file.
--
--   ```lean
--   theorem Catalog.Probability.SeedRec.card_lfsrWords_le_zero_seed(L n : ℕ) :
--       (lfsrWords K L n).card ≤ Fintype.card K ^ (2 * L) - Fintype.card K ^ L + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PRNGZeroSeedBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PRNGZeroSeedBound.lean#L39

-- Thm stub generated from Probability/PRNGZeroSeedBound.lean
import Mathlib
import Definitions.Def_Probability_PRNGEnumerationL1
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGZeroSeedBound

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

open Catalog.Probability.SeedRec

open Finset

variable {K : Type*} [CommRing K] [Fintype K] [DecidableEq K]

theorem Catalog.Probability.SeedRec.card_lfsrWords_le_zero_seed(L n : ℕ) :
    (lfsrWords K L n).card ≤ Fintype.card K ^ (2 * L) - Fintype.card K ^ L + 1 := by sorry
