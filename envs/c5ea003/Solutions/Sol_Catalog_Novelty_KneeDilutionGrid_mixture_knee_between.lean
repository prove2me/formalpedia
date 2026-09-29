-- Prove2me | solution 1 for Catalog.Novelty.KneeDilutionGrid.mixture_knee_between
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:36:11.826692+00:00
-- url     : https://prove2.me/submissions/b1069817-abaf-4a05-9fcf-8f2135137d89

-- Sol generated from Novelty/KneeVariableDilution.lean
import Mathlib
import Definitions.Def_Novelty_KneeDilutionGrid
import Definitions.Def_Novelty_KneeVariableDilution
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_knee_le_of_le
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_le_prefixMass_knee
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_prefixMass_add
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_prefixMass_const_mul
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_prefixMass_lt_of_lt_knee
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_prefixMass_mono

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

/-- Retention is affine in a pointwise mixture of two profiles. -/
theorem prefixMass_mixture (s : ℝ) (p q : ℕ → ℝ) (k : ℕ) :
    prefixMass (fun i => s * p i + (1 - s) * q i) k
      = s * prefixMass p k + (1 - s) * prefixMass q k := by
  rw [prefixMass_add (fun i => s * p i) (fun i => (1 - s) * q i) k,
    prefixMass_const_mul, prefixMass_const_mul]



open Catalog.Novelty.KneeDilutionGrid in
theorem solution{p q : ℕ → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {tau : ℝ}
    (hexp : ∃ k, tau ≤ prefixMass p k) (hexq : ∃ k, tau ≤ prefixMass q k) :
    min (knee p tau) (knee q tau) ≤ knee (fun i => s * p i + (1 - s) * q i) tau ∧
      knee (fun i => s * p i + (1 - s) * q i) tau ≤ max (knee p tau) (knee q tau) := by
  set K1 := knee p tau
  set K2 := knee q tau
  have hp1 : tau ≤ prefixMass p K1 := le_prefixMass_knee hexp
  have hq1 : tau ≤ prefixMass q K2 := le_prefixMass_knee hexq
  have hupper : tau ≤ prefixMass (fun i => s * p i + (1 - s) * q i) (max K1 K2) := by
    rw [prefixMass_mixture]
    have h1 : tau ≤ prefixMass p (max K1 K2) :=
      hp1.trans (prefixMass_mono hp (le_max_left _ _))
    have h2 : tau ≤ prefixMass q (max K1 K2) :=
      hq1.trans (prefixMass_mono hq (le_max_right _ _))
    nlinarith
  refine ⟨?_, knee_le_of_le hupper⟩
  by_contra hcon
  push_neg at hcon
  have hmix : tau ≤ prefixMass (fun i => s * p i + (1 - s) * q i)
      (knee (fun i => s * p i + (1 - s) * q i) tau) := le_prefixMass_knee ⟨_, hupper⟩
  rw [prefixMass_mixture] at hmix
  have h1 : prefixMass p (knee (fun i => s * p i + (1 - s) * q i) tau) < tau :=
    prefixMass_lt_of_lt_knee (lt_of_lt_of_le hcon (min_le_left _ _))
  have h2 : prefixMass q (knee (fun i => s * p i + (1 - s) * q i) tau) < tau :=
    prefixMass_lt_of_lt_knee (lt_of_lt_of_le hcon (min_le_right _ _))
  have key : ∀ A B : ℝ, A < tau → B < tau → tau ≤ s * A + (1 - s) * B → False := by
    intro A B hA hB hAB
    rcases eq_or_lt_of_le hs1 with heq | hslt
    · rw [heq] at hAB
      simp at hAB
      linarith
    · have e1 : s * A ≤ s * tau := mul_le_mul_of_nonneg_left hA.le hs0
      have e2 : (1 - s) * B < (1 - s) * tau := by
        apply mul_lt_mul_of_pos_left hB
        linarith
      nlinarith
  exact key _ _ h1 h2 hmix
