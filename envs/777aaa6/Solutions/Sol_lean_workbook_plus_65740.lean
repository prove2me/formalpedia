-- Prove2me | solution 1 for lean_workbook_plus_65740
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:56:43.790271+00:00
-- url     : https://prove2.me/submissions/683b0218-d8d9-4658-a89a-56d299beb744

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace PairSumQuintic

noncomputable def gap (A B r s : ℝ) : ℝ :=
  A * B * (A + B) * (A - B) ^ 2 + B * r ^ 4 + A * s ^ 4 +
    B * (A - B) * (2 * A - B) * r ^ 2 +
    A * (A - B) * (A - 2 * B) * s ^ 2 + 3 * (A + B) * r ^ 2 * s ^ 2

theorem ordered_gap_nonnegative (A B r s : ℝ) (hB : 0 ≤ B) (hAB : B ≤ A) :
    0 ≤ gap A B r s := by
  have hA : 0 ≤ A := le_trans hB hAB
  have hd : 0 ≤ A - B := by linarith
  have he : 0 ≤ 2 * A - B := by linarith
  by_cases htwo : 2 * B ≤ A
  · have ht : 0 ≤ A - 2 * B := by linarith
    dsimp [gap]
    positivity
  · have ht : 0 ≤ 8 * B - A := by linarith
    have hid : gap A B r s = B * r ^ 4 +
        B * (A - B) * (2 * A - B) * r ^ 2 + 3 * (A + B) * r ^ 2 * s ^ 2 +
        A * (s ^ 2 - (A - B) * (2 * B - A) / 2) ^ 2 +
        A ^ 2 * (A - B) ^ 2 * (8 * B - A) / 4 := by
      dsimp [gap]
      ring
    rw [hid]
    positivity

theorem gap_nonnegative (A B r s : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ gap A B r s := by
  rcases le_total B A with h | h
  · exact ordered_gap_nonnegative A B r s hB h
  · have he : gap A B r s = gap B A s r := by dsimp [gap]; ring
    rw [he]
    exact ordered_gap_nonnegative B A s r hA h

theorem nonnegative_pair_sums (x y z t : ℝ) (hx : 0 ≤ x + t) (hy : 0 ≤ y + z) :
    4 * (y * z * (x ^ 3 + t ^ 3) + x * t * (y ^ 3 + z ^ 3)) ≤
      (x ^ 2 + t ^ 2) ^ 2 * (y + z) + (y ^ 2 + z ^ 2) ^ 2 * (x + t) := by
  have h := gap_nonnegative (x + t) (y + z) (x - t) (y - z) hx hy
  have he : 4 * ((x ^ 2 + t ^ 2) ^ 2 * (y + z) +
      (y ^ 2 + z ^ 2) ^ 2 * (x + t) -
      4 * (y * z * (x ^ 3 + t ^ 3) + x * t * (y ^ 3 + z ^ 3))) =
      gap (x + t) (y + z) (x - t) (y - z) := by
    dsimp [gap]
    ring
  linarith only [h, he]

end PairSumQuintic

theorem solution (h : ∀ x y z t : ℝ,
    4 * (y * z * (x ^ 3 + t ^ 3) + x * t * (y ^ 3 + z ^ 3)) ≤
      (x ^ 2 + t ^ 2) ^ 2 * (y + z) + (y ^ 2 + z ^ 2) ^ 2 * (x + t)) : False := by
  have hc := h (-1) (-2) (-2) (-1)
  norm_num at hc
  change ((4 : ℝ) + 4) ^ 2 * 2 + (1 + 1) ^ 2 * 4 ≤ 96 at hc
  norm_num at hc
