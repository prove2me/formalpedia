-- Prove2me | Theorems.Thm_lean_workbook_plus_47303
-- name    : lean_workbook_plus_47303
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/906fe89a-091f-4288-91b6-f13a0310446e
-- statement:
--   Let $a_1,a_2$ be integers such that $a_1\equiv a_2\pmod{6}$ and let $b$ be an integer. Show that\n\n $$a_1b\equiv a_2b\pmod{6}.$$ \n\nWhat if $b=6$ ? Then the expression would be \n\n $$6a_1b\equiv6a_2b\pmod{6}.$$ If we use the proof we derived in Chapter 14, then $a_1b\equiv a_2b\pmod{1}$ , and there must be a problem here, since there would be infinite possibilities to this congruence.\n\nBy definition, all integers are congruent to each other in modulo $1$ . \n\nSince $a_1$ , $a_2$ and $b$ are all integers, this means that $a_1b\equiv a_2b\pmod1$ , then this means $6a_1b\equiv6a_wb\pmod6$ .\n\nSuppose that we have: \n\n $$a_1\equiv a_2\pmod6$$ If we multiply both sides by $6$ , we discover that $6a_1$ is divisible by $6$ , which means that $6a_1\equiv0\pmod6$ . Similiarly, $6a_2\pmod6$ . \n\nThis shows us that: \n\n $$6a_1\equiv6a_2\pmod6$$ which is what we wanted to prove. \n\nThis is like multiplying both sides by $0$ . Suppose that: \n\n $$x=y$$ If we multiply both sides by $0$ , then $0\cdot x=0$ and $0\cdot y=0$ , which means that: \n\n $$0\cdot x=0\cdot y$$ or \n\n $$0=0$$ which is still true, even though there may be infinitely many possibilities to it.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47303  (a₁ a₂ b : ℤ)
  (h₀ : a₁ ≡ a₂ [ZMOD 6])
  (h₁ : b ≡ b [ZMOD 6]) :
  6 * a₁ * b ≡ 6 * a₂ * b [ZMOD 6]   :=  by sorry
