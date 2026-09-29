-- Prove2me | Theorems.Thm_WorkbookSource_problem_24733
-- name    : WorkbookSource.problem_24733
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:56:36.185733+00:00
-- url     : https://prove2.me/theorems/15ab5872-4892-4ded-a546-f7a1cb95db7b
-- title:
--   Solving a positive square-root equation
-- statement:
--   We let $s$ be the slower boat speed. Then $s+5$ is the faster boats speed. In $2$ hours the slower boat will have gone $2s$ km and in $1$ hours the faster boat will have gone $s+5$ km. We use LoC (Law of Cosines) to find the distance between boats is $\sqrt{(2s)^2+(s+5)^2-2(2s)(s+5)\cos(60^{\circ})}=\sqrt{3s^2+25}$ . Setting $\sqrt{3s^2+25}=10$ gives us $s=5$ km/h.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24733` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24733; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_24733  (s : ℝ)
  (h₀ : 0 < s)
  (h₁ : Real.sqrt (3 * s^2 + 25) = 10) :
  s = 5  :=  by sorry
