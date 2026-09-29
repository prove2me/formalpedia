-- Prove2me | Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_grid_gap_ambiguity
-- name    : Catalog.Novelty.KneeDilutionGrid.grid_gap_ambiguity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:12:36.156991+00:00
-- url     : https://prove2.me/theorems/30a7470f-171f-4871-866b-d569df4f2d50
-- title:
--   A wide gap in the grid is a wide ambiguity in the knee.
-- statement:
--   **A wide gap in the grid is a wide ambiguity in the knee.**  For consecutive
--   budget probes `a < b` there are two nonnegative antitone profiles whose retention
--   agrees at *every* budget outside the open interval `(a, b)` — in particular at
--   every grid point — but whose knees are `a + 1` and `b`.  A grid therefore cannot
--   certify a bracket tighter than the ratio `b / (a + 1)` of its consecutive probes,
--   which is exactly the guarantee that `geometric_grid_brackets_knee` attains with
--   ratio `2`.
--
--   ```lean
--   theorem Catalog.Novelty.KneeDilutionGrid.grid_gap_ambiguity(a b : ℕ) (hab : a < b) :
--       ∃ p q : ℕ → ℝ, (∀ i, 0 ≤ p i) ∧ (∀ i, 0 ≤ q i) ∧ Antitone p ∧ Antitone q ∧
--         (∀ k ≤ a, prefixMass p k = prefixMass q k) ∧
--         (∀ k, b ≤ k → prefixMass p k = prefixMass q k) ∧
--         knee p ((a : ℝ) + 1) = a + 1 ∧ knee q ((a : ℝ) + 1) = b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KneeVariableDilution.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KneeVariableDilution.lean#L246

-- Thm stub generated from Novelty/KneeVariableDilution.lean
import Mathlib
import Definitions.Def_Novelty_KneeDilutionGrid
import Definitions.Def_Novelty_KneeVariableDilution

/-!
# Variable tokenisation, the dilution semigroup, and geometric budget grids (NET-72, round 2)

This file continues `Novelty.KneeDilutionGrid`.  There the tokenisation tax was
modelled by a *uniform* tokens-per-word ratio `r`, and the knee was shown to obey
the multiplicative sandwich `r * (K - 1) < K_split ≤ r * K`.  Real tokenizers are
not uniform: French words cost a variable number of tokens.  Here we

* replace the uniform split by a **variable dilution** `varSplit w p`, where word
  `i` is spelt with `w i ≥ 1` tokens, each carrying an equal share `p i / w i`
  of that word's attention mass;
* prove `variable_dilution_law`: the knee of the diluted profile is sandwiched by
  the *cumulative token counts* of the top words,
  `cum w (K - 1) < knee (varSplit w p) tau ≤ cum w K`, where `K` is the undiluted
  knee.  This is the exact form of the NET-72 mechanism hypothesis: the knee is
  predicted by **tokens-per-word measured on the top-`K` words**, not by any
  additive domain offset;
* derive the two-sided consequence `variable_dilution_between_extremes` in terms
  of the smallest and largest tokens-per-word ratio;
* show the dilution operators form a semigroup, `tokenSplit_comp`, so successive
  domain shifts compose *multiplicatively* (`knee_tokenSplit_comp_le`);
* prove `geometric_grid_brackets_knee`: a geometric budget grid `1, 2, 4, 8, …`
  always brackets the knee within a factor `2`, however large the multiplicative
  tokenisation tax is.  This is the design consequence of the NET-72 failure:
  arithmetic grids (`8, 16, 24, 32`) are the wrong instrument for a
  multiplicative law, geometric grids are the right one.
-/

open Catalog.Novelty.KneeDilutionGrid

open Finset

/-! ### 1. The dilution semigroup -/



/-! ### 2. Variable tokenisation -/
















/-! ### 3. Geometric grids survive a multiplicative tax -/

theorem Catalog.Novelty.KneeDilutionGrid.grid_gap_ambiguity(a b : ℕ) (hab : a < b) :
    ∃ p q : ℕ → ℝ, (∀ i, 0 ≤ p i) ∧ (∀ i, 0 ≤ q i) ∧ Antitone p ∧ Antitone q ∧
      (∀ k ≤ a, prefixMass p k = prefixMass q k) ∧
      (∀ k, b ≤ k → prefixMass p k = prefixMass q k) ∧
      knee p ((a : ℝ) + 1) = a + 1 ∧ knee q ((a : ℝ) + 1) = b := by sorry
