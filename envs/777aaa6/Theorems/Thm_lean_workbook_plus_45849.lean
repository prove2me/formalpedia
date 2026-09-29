-- Prove2me | Theorems.Thm_lean_workbook_plus_45849
-- name    : lean_workbook_plus_45849
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/b8e1ecd7-8636-471e-88d2-a500d5bff06f
-- statement:
--   Let the number of people be $k$ . Then $3k$ handshakes take place, but if $A$ shakes hands with $B$ and $B$ shakes hands with $A$ , then we have counted this same handshake twice. Therefore, $\frac{3k}{2}$ handshakes take place. Hence $3k/2<15$ , so $k<10$ and the maximum value is $k=\boxed{9}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45849  (k : ℕ)
  (h₀ : 0 < k)
  (h₁ : (3 * k / 2) < 15) :
  k < 10   :=  by sorry
