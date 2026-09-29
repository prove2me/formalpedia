-- Prove2me | solution 1 for Catalog.Novelty.KneeDilutionGrid.geometric_grid_brackets_knee
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:21:41.906713+00:00
-- url     : https://prove2.me/submissions/6b1c7c62-5d4d-4876-825a-77cba9ef53a8

-- Sol generated from Novelty/KneeVariableDilution.lean
import Mathlib
import Definitions.Def_Novelty_KneeDilutionGrid
import Definitions.Def_Novelty_KneeVariableDilution
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_knee_exceeds_grid
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_knee_le_of_le
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




open Catalog.Novelty.KneeDilutionGrid in
theorem solution{p : ℕ → ℝ} (hp : ∀ i, 0 ≤ p i) {tau : ℝ}
    (hex : ∃ k, tau ≤ prefixMass p k) :
    ∃ S : ℕ, knee p tau ≤ 2 ^ S ∧ (0 < S → 2 ^ S < 2 * knee p tau) := by
  obtain ⟨k, hk⟩ := hex
  have hkpow : k ≤ 2 ^ k := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hne : Set.Nonempty {i | tau ≤ prefixMass p (2 ^ i)} :=
    ⟨k, le_trans hk (prefixMass_mono hp hkpow)⟩
  set S : ℕ := sInf {i | tau ≤ prefixMass p (2 ^ i)} with hS
  have hSmem : tau ≤ prefixMass p (2 ^ S) := Nat.sInf_mem hne
  refine ⟨S, knee_le_of_le hSmem, ?_⟩
  intro hSpos
  have hprev : prefixMass p (2 ^ (S - 1)) < tau := by
    have hnot : (S - 1) ∉ {i | tau ≤ prefixMass p (2 ^ i)} :=
      Nat.notMem_of_lt_sInf (by omega)
    simpa [Set.mem_setOf_eq, not_le] using hnot
  have hlt : 2 ^ (S - 1) < knee p tau :=
    knee_exceeds_grid hp ⟨2 ^ S, hSmem⟩ hprev
  have hpow : 2 ^ (S - 1) * 2 = 2 ^ S := by
    have h := (pow_succ 2 (S - 1)).symm
    have hS1 : S - 1 + 1 = S := by omega
    rw [hS1] at h
    exact h
  omega
