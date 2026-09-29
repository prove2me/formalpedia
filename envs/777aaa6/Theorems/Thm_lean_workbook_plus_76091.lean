-- Prove2me | Theorems.Thm_lean_workbook_plus_76091
-- name    : lean_workbook_plus_76091
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/8e30f2ba-7ceb-4a4b-b787-237d34eb4b47
-- statement:
--   Here's what I would do: Notice that $50 + 2\sqrt{621}$ and $50 - 2\sqrt{621}$ are both roots of the quadratic $x^2 - 100x + 16$ , and so the sequence $\{a_n\}_{n=0}^{\infty}$ defined by $a_n = (50 + 2\sqrt{621})^{n} + (50 - 2\sqrt{621})^n$ satisfies the recurrence relation $a_n = 100a_{n-1} - 16a_{n-2}$ . This implies that $a_n \equiv - 16a_{n-2} (\bmod{100})$ . Our desired result is just $2(-16)^{25}- 1 \mod{100}$ . Fortunately, the congruences $\mod{100}$ are easy to check and have period $5$ , and we get $2(-16)^5-1 \equiv 47 (\bmod{100})$ as our answer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76091 :
  (2 * (-16 : ℤ)^25 - 1) % 100 = 47   :=  by sorry
