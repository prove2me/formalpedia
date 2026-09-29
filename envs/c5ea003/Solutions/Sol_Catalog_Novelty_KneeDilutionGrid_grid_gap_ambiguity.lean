-- Prove2me | solution 1 for Catalog.Novelty.KneeDilutionGrid.grid_gap_ambiguity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:30:10.162216+00:00
-- url     : https://prove2.me/submissions/a4cb7e9b-90db-46af-a1ed-b9fc5664dfd0

-- Sol generated from Novelty/KneeVariableDilution.lean
import Mathlib
import Definitions.Def_Novelty_KneeDilutionGrid
import Definitions.Def_Novelty_KneeVariableDilution
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_dilution_upper_sharp
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_grid_underdetermines_knee
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_prefixMass_unif
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_unif_antitone
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_unif_nonneg

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




/-! ### 4. Mixed domains -/




open Catalog.Novelty.KneeDilutionGrid in
theorem solution(a b : ℕ) (hab : a < b) :
    ∃ p q : ℕ → ℝ, (∀ i, 0 ≤ p i) ∧ (∀ i, 0 ≤ q i) ∧ Antitone p ∧ Antitone q ∧
      (∀ k ≤ a, prefixMass p k = prefixMass q k) ∧
      (∀ k, b ≤ k → prefixMass p k = prefixMass q k) ∧
      knee p ((a : ℝ) + 1) = a + 1 ∧ knee q ((a : ℝ) + 1) = b := by
  obtain ⟨q, hq0, hqa, hqlow, -, hqhigh, hqk⟩ := grid_underdetermines_knee a b hab
  have hcast : ((a : ℝ) + 1) = ((a + 1 : ℕ) : ℝ) := by push_cast; ring
  refine ⟨unif (a + 1), q, unif_nonneg _, hq0, unif_antitone _, hqa, ?_, ?_, ?_, hqk⟩
  · intro k hk
    rw [prefixMass_unif, hqlow k hk]
    have hmin : min k (a + 1) = k := by omega
    rw [hmin]
  · intro k hk
    rw [prefixMass_unif, hqhigh k hk]
    have hmin : min k (a + 1) = a + 1 := by omega
    rw [hmin]
    push_cast
    ring
  · rw [hcast]
    exact (dilution_upper_sharp 1 (a + 1) (a + 1) one_pos le_rfl).1
