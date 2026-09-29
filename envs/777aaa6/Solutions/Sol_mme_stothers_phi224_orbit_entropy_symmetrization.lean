-- Prove2me | solution 1 for mme_stothers_phi224_orbit_entropy_symmetrization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:34:03.297089+00:00
-- url     : https://prove2.me/submissions/038f326b-5382-4011-9479-afde14965059

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

open BigOperators

set_option autoImplicit false
set_option warningAsError true

private theorem negMulLog_pair_average
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog x + Real.negMulLog y ≤
      2 * Real.negMulLog ((x + y) / 2) := by
  have hconc :
      Convex ℝ (Set.Ici (0 : ℝ)) ∧
        ∀ ⦃u⦄, u ∈ Set.Ici (0 : ℝ) →
          ∀ ⦃v⦄, v ∈ Set.Ici (0 : ℝ) →
            ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
              a • Real.negMulLog u + b • Real.negMulLog v ≤
                Real.negMulLog (a • u + b • v) :=
    Real.concaveOn_negMulLog
  have h := @hconc.2 x hx y hy ((1 : ℝ) / 2) ((1 : ℝ) / 2)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [smul_eq_mul] at h ⊢
  have harg : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y = (x + y) / 2 := by
    ring
  rw [harg] at h
  linarith

theorem solution
    (x : Fin 9 → ℝ) (hx : ∀ r, 0 ≤ x r) :
    (∑ r : Fin 9, Real.negMulLog (x r)) ≤
      2 * Real.negMulLog ((x 0 + x 8) / 2) +
      4 * Real.negMulLog ((x 1 + x 3 + x 5 + x 7) / 4) +
      2 * Real.negMulLog ((x 2 + x 6) / 2) +
      Real.negMulLog (x 4) := by
  have h08 := negMulLog_pair_average (x 0) (x 8) (hx 0) (hx 8)
  have h17 := negMulLog_pair_average (x 1) (x 7) (hx 1) (hx 7)
  have h35 := negMulLog_pair_average (x 3) (x 5) (hx 3) (hx 5)
  have h26 := negMulLog_pair_average (x 2) (x 6) (hx 2) (hx 6)
  have havg :
      Real.negMulLog ((x 1 + x 7) / 2) +
          Real.negMulLog ((x 3 + x 5) / 2) ≤
        2 * Real.negMulLog ((x 1 + x 3 + x 5 + x 7) / 4) := by
    have h := negMulLog_pair_average
      ((x 1 + x 7) / 2) ((x 3 + x 5) / 2)
      (by linarith [hx 1, hx 7]) (by linarith [hx 3, hx 5])
    have harg :
        (((x 1 + x 7) / 2 + (x 3 + x 5) / 2) / 2) =
          (x 1 + x 3 + x 5 + x 7) / 4 := by
      ring
    simpa only [harg] using h
  simp [Fin.sum_univ_succ]
  linarith
