-- Prove2me | solution 1 for Catalog.Novelty.KneeDilutionGrid.varSplit_const
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:36:13.262262+00:00
-- url     : https://prove2.me/submissions/8447b3f8-c4b6-4384-81d9-f6ff15af3985

-- Sol generated from Novelty/KneeVariableDilution.lean
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


lemma cum_succ (w : ℕ → ℕ) (m : ℕ) : cum w (m + 1) = cum w m + w m := Finset.sum_range_succ _ _

lemma cum_mono (w : ℕ → ℕ) : Monotone (cum w) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset (by simpa using hab)



lemma wordOf_eq {w : ℕ → ℕ} (m t : ℕ) (ht : t < w m) : wordOf w (cum w m + t) = m := by
  have hmem : cum w m + t < cum w (m + 1) := by rw [cum_succ]; omega
  have hne : Set.Nonempty {m' | cum w m + t < cum w (m' + 1)} := ⟨m, hmem⟩
  have h2 : cum w m + t < cum w (wordOf w (cum w m + t) + 1) := Nat.sInf_mem hne
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra hcon
  push_neg at hcon
  have hle : cum w (wordOf w (cum w m + t) + 1) ≤ cum w m := cum_mono w (by omega)
  omega










/-! ### 3. Geometric grids survive a multiplicative tax -/




/-! ### 4. Mixed domains -/




open Catalog.Novelty.KneeDilutionGrid in
theorem solution(r : ℕ) (hr : 0 < r) (p : ℕ → ℝ) :
    varSplit (fun _ => r) p = tokenSplit r p := by
  funext j
  have hcum : ∀ m, cum (fun _ => r) m = r * m := by
    intro m
    induction m with
    | zero => simp [cum]
    | succ m ih => rw [cum_succ, ih]; ring
  have hmod : j % r < r := Nat.mod_lt _ hr
  have hj : j = cum (fun _ => r) (j / r) + j % r := by
    rw [hcum]
    have := Nat.div_add_mod j r
    omega
  have hword : wordOf (fun _ => r) j = j / r := by
    conv_lhs => rw [hj]
    exact wordOf_eq (w := fun _ => r) (j / r) (j % r) hmod
  simp only [varSplit, tokenSplit, hword]
