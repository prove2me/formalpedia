-- Prove2me | Theorems.Thm_lean_workbook_plus_46480
-- name    : lean_workbook_plus_46480
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/33e94a61-b44b-46bc-9b4d-b85bb145af74
-- statement:
--   Let $m$ be the cost of her monthly bill and $t$ be her hourly charge. We now have a system of equations: $m + t = 12.48$ . $m + 2t = 17.54$ . Subtracting the bottom equation from the top equation, we have $t = 5.06$ . Since, $m = 12.48 - t$ , we now know that $m = 12.48 - 5.06 = 7.42$ . Therefore, the answer is $\fbox{(D)7.42}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46480  (m t : ℝ)
  (h₀ : m + t = 12.48)
  (h₁ : m + 2 * t = 17.54) :
  m = 7.42   :=  by sorry
