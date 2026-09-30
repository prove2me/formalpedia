-- Prove2me | solution 1 for lean_workbook_plus_63103
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T03:37:34.815452+00:00
-- url     : https://prove2.me/submissions/faf55ead-18b1-425d-9684-44fda2144a34

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

theorem solution : ¬ (∀ (a b c d e : ℝ) (f : ℝ → ℝ),
    (∀ x, f x = a * x^4 + b * x^3 + c * x^2 + d * x + e) →
    f 1 = 1 / (1^2 * (1 + 1)) →
    f 2 = 1 / (2^2 * (2 + 1)) →
    f 3 = 1 / (3^2 * (3 + 1)) →
    f 4 = 1 / (4^2 * (4 + 1)) →
    f 5 = 1 / (5^2 * (5 + 1)) →
    20 * (a - b + c - d + e) = 29) := by
  intro h
  let p : ℝ → ℝ := fun x =>
    (29 / 2400) * x^4 + (-251 / 1440) * x^3 +
      (1331 / 1440) * x^2 + (-3097 / 1440) * x + 6799 / 3600
  have hp := h (29 / 2400) (-251 / 1440) (1331 / 1440)
    (-3097 / 1440) (6799 / 3600) p (by intro x; rfl)
    (by norm_num [p]) (by norm_num [p]) (by norm_num [p])
    (by norm_num [p]) (by norm_num [p])
  norm_num at hp
