-- Prove2me | solution 1 for Catalog.Novelty.KneeDilutionGrid.prefixMass_tokenSplit_block
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:30:11.142793+00:00
-- url     : https://prove2.me/submissions/273a7e5e-68ad-4b5a-8ffc-be26074b5a14

-- Sol generated from Novelty/KneeDilutionGrid.lean
import Mathlib
import Definitions.Def_Novelty_KneeDilutionGrid

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



@[simp] lemma prefixMass_zero (p : ℕ → ℝ) : prefixMass p 0 = 0 := by simp [prefixMass]









/-! ### 2. A failed grid sweep bounds the knee only from below -/




/-! ### 3. Flat and two-level profiles (the calibration objects) -/











/-! ### 4. A grid reading determines nothing above the grid -/







/-! ### 5. The tokenisation mechanism: mass-preserving dilution -/




private lemma tokenSplit_blockSum (r : ℕ) (hr : 0 < r) (p : ℕ → ℝ) (m s : ℕ) (hs : s ≤ r) :
    ∑ i ∈ range s, tokenSplit r p (r * m + i) = s * (p m / r) := by
  have h : ∀ i ∈ range s, tokenSplit r p (r * m + i) = p m / r := by
    intro i hi
    have hir : i < r := lt_of_lt_of_le (mem_range.1 hi) hs
    simp only [tokenSplit]
    rw [Nat.mul_add_div hr, Nat.div_eq_of_lt hir]
    simp
  rw [Finset.sum_congr rfl h, Finset.sum_const, card_range, nsmul_eq_mul]







/-! ### 6. Sharpness of the dilution law -/




/-! ### 7. No additive domain-shift law -/


/-! ### 8. Accuracy and knee are logically independent -/





open Catalog.Novelty.KneeDilutionGrid in
theorem solution(r : ℕ) (hr : 0 < r) (p : ℕ → ℝ) (m : ℕ) :
    prefixMass (tokenSplit r p) (r * m) = prefixMass p m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h1 : r * (m + 1) = r * m + r := by ring
      rw [h1]
      unfold prefixMass at *
      rw [Finset.sum_range_add, ih, Finset.sum_range_succ]
      congr 1
      rw [tokenSplit_blockSum r hr p m r le_rfl]
      field_simp
