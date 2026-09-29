-- Prove2me | Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_geometric_grid_brackets_knee
-- name    : Catalog.Novelty.KneeDilutionGrid.geometric_grid_brackets_knee
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:12:11.191856+00:00
-- url     : https://prove2.me/theorems/3a3b02a4-9d2e-4d00-83a7-5c4b310a8fe2
-- title:
--   A geometric sweep always brackets the knee within a factor two.
-- statement:
--   **A geometric sweep always brackets the knee within a factor two.**  Let `S`
--   be the least exponent whose budget `2 ^ S` meets the bar.  Then
--   `knee ≤ 2 ^ S` and, unless `S = 0`, `2 ^ S < 2 * knee`.  Unlike an arithmetic
--   grid, a geometric grid cannot be escaped by a multiplicative domain tax: the
--   tax only shifts `S` by `log 2 r`.  This is the experimental design correction
--   implied by the NET-72 failure.
--
--   ```lean
--   theorem Catalog.Novelty.KneeDilutionGrid.geometric_grid_brackets_knee{p : ℕ → ℝ} (hp : ∀ i, 0 ≤ p i) {tau : ℝ}
--       (hex : ∃ k, tau ≤ prefixMass p k) :
--       ∃ S : ℕ, knee p tau ≤ 2 ^ S ∧ (0 < S → 2 ^ S < 2 * knee p tau) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KneeVariableDilution.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KneeVariableDilution.lean#L199

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

theorem Catalog.Novelty.KneeDilutionGrid.geometric_grid_brackets_knee{p : ℕ → ℝ} (hp : ∀ i, 0 ≤ p i) {tau : ℝ}
    (hex : ∃ k, tau ≤ prefixMass p k) :
    ∃ S : ℕ, knee p tau ≤ 2 ^ S ∧ (0 < S → 2 ^ S < 2 * knee p tau) := by sorry
