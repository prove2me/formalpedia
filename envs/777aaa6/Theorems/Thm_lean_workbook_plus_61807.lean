-- Prove2me | Theorems.Thm_lean_workbook_plus_61807
-- name    : lean_workbook_plus_61807
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/2a909b80-c4b2-4577-87c0-dfe281923913
-- statement:
--   Let $ P(x) $ be a linear function, $P(x)=ax+b$ . Then, if this works out, our answer will be just $a^2+b^2$ , because the remainder when a linear function $P(x)$ is divided by a quadratic is just $P(x)$ . Now, using synthetic division, the remainder when $ ax+b $ is divided by $ x - 2 $ is $ b + 2a = 3 $ . Similarly, for $x-3$ , the remainder is $ b + 3a = 2 $ . Solving, we get $ a = -1 $ and $ b = 5 $ , so the function is $ P(x) = -x + 5. $ Success! Our answer is $(-1)^2+5^2=\boxed{26}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61807  (a b : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x + b)
  (h₁ : f 2 = 3)
  (h₂ : f 3 = 2) :
  a^2 + b^2 = 26   :=  by sorry
