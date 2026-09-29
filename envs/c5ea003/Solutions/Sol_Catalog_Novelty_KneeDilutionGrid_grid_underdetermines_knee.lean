-- Prove2me | solution 1 for Catalog.Novelty.KneeDilutionGrid.grid_underdetermines_knee
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:22:58.135191+00:00
-- url     : https://prove2.me/submissions/073edaeb-ecc4-4ed8-8715-1fa52b0f9c3a

-- Sol generated from Novelty/KneeDilutionGrid.lean
import Mathlib
import Definitions.Def_Novelty_KneeDilutionGrid
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_knee_eq_of
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_prefixMass_add
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_prefixMass_const_mul
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_prefixMass_unif

/-!
# The knee of an attention budget: grids, dilution, and the French anomaly (NET-72)

This file formalises the structural content of the NET-72 measurement
**THE-FRENCH-KNEE-EXCEEDS-THE-GRID**.

The empirical situation: a limited-memory (top-`k` key retention) sweep over the
budget grid `{…, 24}` at context 512 and `{…, 32}` at context 1024 found that on
French prose *no* grid point reached the retention bar (`0.9648` and `0.9680`
retained at the best grid point).  On English prose, code and mathematics the
knee had always been inside the grid, and the observed domain shifts were small
(`±4` keys — "one fine-step").  French broke the bracket.

We prove five things about the underlying mathematics, using an **attention
profile** `p : ℕ → ℝ` (the attention mass carried by the `i`-th most important
key, so `p` is nonnegative and antitone), its prefix mass `prefixMass p k`
(the mass retained by a budget of `k` keys), and the **knee**
`knee p tau = sInf {k | tau ≤ prefixMass p k}` (the least budget meeting the bar).

* `knee_exceeds_grid`, `knee_exceeds_grid_max`, `net72_french_knee_beyond_grid` —
  the honest reading of a failed sweep: if every grid point falls below the bar
  then the knee is *strictly larger than every grid point*.  A grid can only ever
  certify a **lower** bound on the knee.
* `grid_underdetermines_knee` — and that lower bound is all one gets: for every
  target `N` beyond the grid there is a profile with *exactly the same retention
  at every grid point*, and knee exactly `N`.  So "knee > 32" is not evidence for
  "knee = 36"; the size of the excess is invisible to the sweep.
* `dilution_law` — the tokenisation mechanism, exactly.  If a domain shift splits
  every semantic unit into `r` tokens of equal share (mass-preserving dilution
  `tokenSplit`), then the knee scales *multiplicatively*:
  `r * (knee p tau - 1) < knee (tokenSplit r p) tau ≤ r * knee p tau`.
  Both ends are attained (`dilution_upper_sharp`, `dilution_lower_sharp`), so the
  sandwich cannot be tightened.
* `no_additive_domain_shift_law` — the refutation of the "±4 fine-step" law:
  for **every** offset `d` there is a profile and a tokens-per-word ratio for
  which the knee jumps by more than `d`.  A multiplicative law admits no uniform
  additive bracket, which is precisely why French escaped the grid.
* `accuracy_knee_decoupling` — full-context accuracy and the knee are logically
  independent: two domains with the *same* accuracies can have the knee ordering
  in either direction ("code: easier and cheaper", "French: easier and dearer").

All constants are explicit; nothing is asymptotic.
-/

open Catalog.Novelty.KneeDilutionGrid

open Finset

/-! ### 1. Profiles, retained mass, and the knee -/












/-! ### 2. A failed grid sweep bounds the knee only from below -/




/-! ### 3. Flat and two-level profiles (the calibration objects) -/











/-! ### 4. A grid reading determines nothing above the grid -/


lemma twoLevel_apply {g N : ℕ} (hgN : g ≤ N) (c : ℝ) (i : ℕ) :
    twoLevel g N c i = if i < g then 1 else if i < N then c else 0 := by
  unfold twoLevel unif
  split_ifs <;> first | omega | ring

lemma twoLevel_nonneg {g N : ℕ} (hgN : g ≤ N) {c : ℝ} (hc : 0 ≤ c) :
    ∀ i, 0 ≤ twoLevel g N c i := by
  intro i
  rw [twoLevel_apply hgN]
  split_ifs <;> first | exact hc | norm_num

lemma twoLevel_antitone {g N : ℕ} (hgN : g ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Antitone (twoLevel g N c) := by
  refine antitone_nat_of_succ_le ?_
  intro i
  rw [twoLevel_apply hgN, twoLevel_apply hgN]
  split_ifs <;> first | omega | linarith

lemma prefixMass_twoLevel (g N : ℕ) (c : ℝ) (k : ℕ) :
    prefixMass (twoLevel g N c) k = (min k g : ℕ) + c * ((min k N : ℕ) - (min k g : ℕ)) := by
  unfold twoLevel
  rw [prefixMass_add (unif g) (fun i => c * (unif N i - unif g i)) k, prefixMass_unif]
  congr 1
  have h : (fun i => c * (unif N i - unif g i)) = fun i => c * unif N i + (-c) * unif g i := by
    funext i; ring
  rw [h, prefixMass_add, prefixMass_const_mul, prefixMass_const_mul,
    prefixMass_unif, prefixMass_unif]
  ring


/-! ### 5. The tokenisation mechanism: mass-preserving dilution -/











/-! ### 6. Sharpness of the dilution law -/




/-! ### 7. No additive domain-shift law -/


/-! ### 8. Accuracy and knee are logically independent -/





open Catalog.Novelty.KneeDilutionGrid in
theorem solution(g N : ℕ) (hgN : g < N) :
    ∃ p : ℕ → ℝ, (∀ i, 0 ≤ p i) ∧ Antitone p ∧
      (∀ k ≤ g, prefixMass p k = k) ∧
      (∀ k ≤ g, prefixMass p k < (g : ℝ) + 1) ∧
      (∀ k, N ≤ k → prefixMass p k = (g : ℝ) + 1) ∧
      knee p ((g : ℝ) + 1) = N := by
  have hNg : (0 : ℝ) < (N : ℝ) - g := by
    have : (g : ℝ) < N := by exact_mod_cast hgN
    linarith
  set c : ℝ := 1 / ((N : ℝ) - g) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one hNg]
    have : (g : ℝ) + 1 ≤ N := by exact_mod_cast hgN
    linarith
  refine ⟨twoLevel g N c, twoLevel_nonneg hgN.le hc0.le, twoLevel_antitone hgN.le hc0.le hc1,
    ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [prefixMass_twoLevel]
    have e1 : min k g = k := by omega
    have e2 : min k N = k := by omega
    rw [e1, e2]; ring
  · intro k hk
    rw [prefixMass_twoLevel]
    have e1 : min k g = k := by omega
    have e2 : min k N = k := by omega
    rw [e1, e2]
    have hkg : (k : ℝ) ≤ g := by exact_mod_cast hk
    simp only [sub_self, mul_zero, add_zero]
    linarith
  · intro k hk
    rw [prefixMass_twoLevel]
    have e1 : min k g = g := by omega
    have e2 : min k N = N := by omega
    rw [e1, e2, hc]
    field_simp
  · refine knee_eq_of ?_ ?_
    · rw [prefixMass_twoLevel]
      have e1 : min N g = g := by omega
      have e2 : min N N = N := by omega
      rw [e1, e2, hc]
      field_simp
      exact le_rfl
    · intro j hj
      rw [prefixMass_twoLevel]
      have e2 : min j N = j := by omega
      rw [e2, hc]
      rcases le_or_gt j g with h | h
      · have e1 : min j g = j := by omega
        rw [e1]
        have hjg : (j : ℝ) ≤ g := by exact_mod_cast h
        simp only [sub_self, mul_zero, add_zero]
        linarith
      · have e1 : min j g = g := by omega
        rw [e1]
        have hjg : (j : ℝ) - g < (N : ℝ) - g := by
          have : (j : ℝ) < N := by exact_mod_cast hj
          linarith
        rw [div_mul_eq_mul_div, one_mul]
        have hlt1 : ((j : ℝ) - g) / ((N : ℝ) - g) < 1 := (div_lt_one hNg).2 hjg
        linarith
