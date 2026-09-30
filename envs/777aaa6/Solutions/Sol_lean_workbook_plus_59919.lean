-- Prove2me | solution 1 for lean_workbook_plus_59919
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:40.190032+00:00
-- url     : https://prove2.me/submissions/af2d9c29-6048-4423-a5c2-0d4ed3d8260e

import Mathlib.Tactic.NormNum

theorem negative_pell_no_integer_solution (x y : ℤ) : x ^ 2 - 6 * y ^ 2 ≠ -3 := by
  have hfinite : ∀ a b : Fin 9,
      ((a.val : ℤ) ^ 2 - 6 * (b.val : ℤ) ^ 2) % 9 ≠ 6 := by decide
  let a : Fin 9 := ⟨(x % 9).toNat, by omega⟩
  let b : Fin 9 := ⟨(y % 9).toNat, by omega⟩
  have ha : (a.val : ℤ) = x % 9 := by dsimp [a]; omega
  have hb : (b.val : ℤ) = y % 9 := by dsimp [b]; omega
  have hn := hfinite a b
  rw [ha, hb] at hn
  have hreduce : ((x % 9) ^ 2 - 6 * (y % 9) ^ 2) % 9 =
      (x ^ 2 - 6 * y ^ 2) % 9 := by
    simp only [pow_two, Int.sub_emod, Int.mul_emod, Int.emod_emod]
  intro h
  apply hn
  rw [hreduce, h]
  norm_num

theorem solution (x y : ℤ) (_hpos : 0 < x ∧ 0 < y)
    (h : x ^ 2 - 6 * y ^ 2 = -3) : x = 3 ∧ y = 1 := by
  exact False.elim (negative_pell_no_integer_solution x y h)
