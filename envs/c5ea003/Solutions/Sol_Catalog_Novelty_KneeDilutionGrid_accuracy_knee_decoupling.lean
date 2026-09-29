-- Prove2me | solution 1 for Catalog.Novelty.KneeDilutionGrid.accuracy_knee_decoupling
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:15:20.808185+00:00
-- url     : https://prove2.me/submissions/289ab38d-9716-4870-8090-66f90b9e7c4f

-- Sol generated from Novelty/KneeDilutionGrid.lean
import Mathlib
import Definitions.Def_Novelty_KneeDilutionGrid
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_knee_scaled
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_unif_antitone
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_unif_nonneg

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






lemma scaled_nonneg {c : ℝ} (hc : 0 ≤ c) (n : ℕ) : ∀ i, 0 ≤ scaled c n i := fun i =>
  mul_nonneg hc (unif_nonneg n i)

lemma scaled_antitone {c : ℝ} (hc : 0 ≤ c) (n : ℕ) : Antitone (scaled c n) := by
  intro a b hab
  exact mul_le_mul_of_nonneg_left (unif_antitone n hab) hc




/-! ### 4. A grid reading determines nothing above the grid -/







/-! ### 5. The tokenisation mechanism: mass-preserving dilution -/











/-! ### 6. Sharpness of the dilution law -/




/-! ### 7. No additive domain-shift law -/


/-! ### 8. Accuracy and knee are logically independent -/





open Catalog.Novelty.KneeDilutionGrid in
theorem solution:
    ∃ D1 D2 D3 D4 : DomainCell,
      D1.acc = D3.acc ∧ D2.acc = D4.acc ∧ D1.acc < D2.acc ∧
      D1.knee 1 < D2.knee 1 ∧ D4.knee 1 < D3.knee 1 := by
  have hA : knee (scaled 1 4) 1 = 1 := by
    refine knee_scaled (by omega) ?_ ?_
    · norm_num
    · intro j hj
      interval_cases j
      norm_num
  have hB : knee (scaled (1 / 2) 4) 1 = 2 := by
    refine knee_scaled (by omega) ?_ ?_
    · norm_num
    · intro j hj
      interval_cases j <;> norm_num
  refine ⟨⟨0, scaled 1 4, scaled_nonneg zero_le_one 4, scaled_antitone zero_le_one 4⟩,
          ⟨1, scaled (1 / 2) 4, scaled_nonneg (by norm_num) 4, scaled_antitone (by norm_num) 4⟩,
          ⟨0, scaled (1 / 2) 4, scaled_nonneg (by norm_num) 4, scaled_antitone (by norm_num) 4⟩,
          ⟨1, scaled 1 4, scaled_nonneg zero_le_one 4, scaled_antitone zero_le_one 4⟩,
          rfl, rfl, by norm_num, ?_, ?_⟩
  · show knee (scaled 1 4) 1 < knee (scaled (1 / 2) 4) 1
    rw [hA, hB]; omega
  · show knee (scaled 1 4) 1 < knee (scaled (1 / 2) 4) 1
    rw [hA, hB]; omega
