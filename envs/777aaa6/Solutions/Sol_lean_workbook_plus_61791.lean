-- Prove2me | solution 1 for lean_workbook_plus_61791
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:02:07.104571+00:00
-- url     : https://prove2.me/submissions/5d92b46b-c635-47e4-862a-674e4c3979df

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace SymmetricSexticProduct

theorem gap_identity (x y z : ℝ) :
    8 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 -
        9 * (x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y) =
      3 / 2 * ((x ^ 3 - y ^ 3) ^ 2 + (y ^ 3 - z ^ 3) ^ 2 + (z ^ 3 - x ^ 3) ^ 2) +
        (x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z) *
          (5 * (x ^ 3 + y ^ 3 + z ^ 3) + 6 * x * y * z) := by ring

theorem cubic_amgm (x y z : ℝ) (hs : 0 ≤ x + y + z) :
    0 ≤ x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z := by
  have h := mul_nonneg hs
    (add_nonneg (add_nonneg (sq_nonneg (x - y)) (sq_nonneg (y - z)))
      (sq_nonneg (z - x)))
  nlinarith

theorem inequality (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    9 * (x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y) ≤
      8 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 := by
  have hcoef : 0 ≤ 5 * (x ^ 3 + y ^ 3 + z ^ 3) + 6 * x * y * z := by positivity
  have hprod := mul_nonneg (cubic_amgm x y z (by positivity)) hcoef
  nlinarith [gap_identity x y z, sq_nonneg (x ^ 3 - y ^ 3),
    sq_nonneg (y ^ 3 - z ^ 3), sq_nonneg (z ^ 3 - x ^ 3)]

theorem equality_iff (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    8 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 =
      9 * (x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y) ↔
        x = y ∧ y = z := by
  constructor
  · intro h
    have hcoef : 0 ≤ 5 * (x ^ 3 + y ^ 3 + z ^ 3) + 6 * x * y * z := by positivity
    have hprod := mul_nonneg (cubic_amgm x y z (by positivity)) hcoef
    have heq := gap_identity x y z
    have hxy : x ^ 3 = y ^ 3 := by
      nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (y ^ 3 - z ^ 3),
        sq_nonneg (z ^ 3 - x ^ 3)]
    have hyz : y ^ 3 = z ^ 3 := by
      nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (y ^ 3 - z ^ 3),
        sq_nonneg (z ^ 3 - x ^ 3)]
    exact ⟨(pow_left_inj₀ hx hy (by decide : (3 : ℕ) ≠ 0)).mp hxy,
      (pow_left_inj₀ hy hz (by decide : (3 : ℕ) ≠ 0)).mp hyz⟩
  · rintro ⟨rfl, rfl⟩
    ring

end SymmetricSexticProduct

theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) :
    8 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 ≥
      9 * (x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y) :=
  SymmetricSexticProduct.inequality x y z hx hy hz
