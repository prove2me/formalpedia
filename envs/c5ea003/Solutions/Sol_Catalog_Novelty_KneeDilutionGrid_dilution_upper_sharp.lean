-- Prove2me | solution 1 for Catalog.Novelty.KneeDilutionGrid.dilution_upper_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:16:48.350625+00:00
-- url     : https://prove2.me/submissions/20cb047b-529a-41bc-af82-d48b42cab49a

-- Sol generated from Novelty/KneeDilutionGrid.lean
import Mathlib
import Definitions.Def_Novelty_KneeDilutionGrid
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_knee_scaled

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









lemma unif_eq_scaled (n : ℕ) : unif n = scaled 1 n := by funext i; simp [scaled]


/-! ### 4. A grid reading determines nothing above the grid -/







/-! ### 5. The tokenisation mechanism: mass-preserving dilution -/











/-! ### 6. Sharpness of the dilution law -/

lemma tokenSplit_unif (r n : ℕ) (hr : 0 < r) :
    tokenSplit r (unif n) = scaled (1 / r) (r * n) := by
  funext j
  have hcomm : n * r = r * n := Nat.mul_comm n r
  simp only [tokenSplit, scaled, unif]
  by_cases h : j < r * n
  · have hj : j / r < n := by rw [Nat.div_lt_iff_lt_mul hr, hcomm]; exact h
    simp [hj, h]
  · have hj : ¬ j / r < n := by rw [Nat.div_lt_iff_lt_mul hr, hcomm]; exact h
    simp [hj, h]



/-! ### 7. No additive domain-shift law -/


/-! ### 8. Accuracy and knee are logically independent -/





open Catalog.Novelty.KneeDilutionGrid in
theorem solution(r m n : ℕ) (hr : 0 < r) (hmn : m ≤ n) :
    knee (unif n) (m : ℝ) = m ∧ knee (tokenSplit r (unif n)) (m : ℝ) = r * m := by
  constructor
  · rw [unif_eq_scaled]
    refine knee_scaled hmn ?_ ?_
    · simp
    · intro j hj
      have hjm : (j : ℝ) < m := by exact_mod_cast hj
      simpa using hjm
  · rw [tokenSplit_unif r n hr]
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    refine knee_scaled (Nat.mul_le_mul_left r hmn) ?_ ?_
    · push_cast
      field_simp
      exact le_rfl
    · intro j hj
      have hjR : (j : ℝ) < (r : ℝ) * m := by exact_mod_cast hj
      rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hrR]
      linarith
