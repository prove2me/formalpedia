-- Prove2me | solution 1 for lean_workbook_plus_73446
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:14:22.83129+00:00
-- url     : https://prove2.me/submissions/dd64c9d5-bcff-4103-8791-7b8f5fa9f83b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c d : ℝ) (p : ℝ → ℝ)
    (hp : p = fun x : ℝ => x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d) :
    p 1 = 827 ∧ p 2 = 1654 ∧ p 3 = 2481 → (p 9 + p (-5)) / 4 = 2003 := by
  rintro ⟨h1, h2, h3⟩
  have heval : p 9 + p (-5) = 49 * p 1 - 96 * p 2 + 49 * p 3 + 4704 := by
    rw [hp]
    dsimp
    ring
  rw [heval, h1, h2, h3]
  norm_num
