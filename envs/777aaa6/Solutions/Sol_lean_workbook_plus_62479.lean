-- Prove2me | solution 1 for lean_workbook_plus_62479
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:02:14.33729+00:00
-- url     : https://prove2.me/submissions/dc78b147-467b-4a5b-8533-810f1a62f22c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace MonicQuarticReflection

theorem coefficient_classification (a b c d : ℝ)
    (h1 : 1 + a + b + c + d = 10)
    (h2 : 16 + 8 * a + 4 * b + 2 * c + d = 20)
    (h3 : 81 + 27 * a + 9 * b + 3 * c + d = 30) :
    b = -6 * a - 25 ∧ c = 11 * a + 70 ∧ d = -6 * a - 36 := by
  constructor
  · linarith
  constructor <;> linarith

theorem factorization (a x : ℝ) :
    x ^ 4 + a * x ^ 3 + (-6 * a - 25) * x ^ 2 + (11 * a + 70) * x +
        (-6 * a - 36) =
      10 * x + (x - 1) * (x - 2) * (x - 3) * (x + a + 6) := by ring

theorem reflection_identity (a b c d : ℝ) (P : ℝ → ℝ)
    (hP : P = fun x => x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d)
    (h : P 1 = 10 ∧ P 2 = 20 ∧ P 3 = 30) (x : ℝ) :
    P x + P (4 - x) = 40 + 2 * (x - 1) * (x - 2) ^ 2 * (x - 3) := by
  subst P
  rcases h with ⟨h1, h2, h3⟩
  norm_num at h1 h2 h3
  obtain ⟨rfl, rfl, rfl⟩ := coefficient_classification a b c d
    (by linarith) (by linarith) (by linarith)
  dsimp
  ring

end MonicQuarticReflection

theorem solution (a b c d : ℝ) (P : ℝ → ℝ)
    (hP : P = fun x => x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d) :
    P 1 = 10 ∧ P 2 = 20 ∧ P 3 = 30 → P 10 + P (-6) = 8104 := by
  intro h
  have hr := MonicQuarticReflection.reflection_identity a b c d P hP h 10
  norm_num at hr
  change P 10 + P (-6) = (40 : ℝ) + 8064 at hr
  linarith
