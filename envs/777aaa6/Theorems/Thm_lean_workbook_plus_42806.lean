-- Prove2me | Theorems.Thm_lean_workbook_plus_42806
-- name    : lean_workbook_plus_42806
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/e59281bf-9079-443f-9094-ff2fc9808ffe
-- statement:
--   Let, $ p$ be the probability that the first archer wins. Take the first aim. The first archer wins on that aim with probability $ \frac{1}{2}$ and with probability $ \frac{1}{2},$ the game continues to the second shot. The moment that happens, it's just as if we were starting over, except that the roles are now reversed - and the first archer's overall winning probability, given that he didn't win on the first shot, is $ 1-p.$ So $ p=\frac{1}{2}+\frac{1}{2}\cdot(1-p)\implies \frac 32p=1\implies p=\frac 23$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42806  (p : ℝ)
  (h₀ : p = 1 / 2 + 1 / 2 * (1 - p)) :
  p = 2 / 3   :=  by sorry
