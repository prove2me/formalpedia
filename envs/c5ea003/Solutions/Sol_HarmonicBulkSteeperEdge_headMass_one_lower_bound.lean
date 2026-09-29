-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.headMass_one_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T02:42:10.561144+00:00
-- url     : https://prove2.me/submissions/6d148d2a-c1ad-4c2a-9d98-efba404a4d2d

import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge
open HarmonicBulkSteeperEdge Finset in
theorem solution {m n : ℕ} (hn : 1 ≤ n) :
    headSum 1 m / (1 + Real.log n) ≤ headMass 1 n m := by
  -- at exponent `1` the head sum is the harmonic number
  have hH : ∀ t : ℕ, headSum 1 t = (harmonic t : ℝ) := by
    intro t
    induction t with
    | zero => simp [headSum]
    | succ t ih =>
      rw [harmonic_succ, headSum, sum_Icc_succ_top (by omega), ← headSum, ih]
      unfold pw
      rw [Real.rpow_neg_one]
      push_cast
      ring
  have hpos : 0 < headSum 1 n := by
    rw [hH]
    exact_mod_cast harmonic_pos (by omega)
  have hnn : 0 ≤ headSum 1 m := by
    unfold headSum pw
    exact sum_nonneg fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hle : headSum 1 n ≤ 1 + Real.log n := by
    rw [hH]
    exact harmonic_le_one_add_log n
  unfold headMass
  exact div_le_div_of_nonneg_left hnn hpos hle
