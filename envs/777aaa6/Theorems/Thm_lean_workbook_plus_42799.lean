-- Prove2me | Theorems.Thm_lean_workbook_plus_42799
-- name    : lean_workbook_plus_42799
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/b8292e56-c53f-437a-bd87-cc332608b0f8
-- statement:
--   Vieta's gives that $\frac{m_k}{18} = 2 \iff m_k = 36$ . We now have $36 = 6f + 9g$ . Taking it $\pmod{6}$ we get $0 \equiv 3g \pmod{6} \iff g\in\{0,2,4\}$ . Taking it $\pmod{9}$ we get $0\equiv6f\pmod{9}\iff f\in\{0,3,6\}$ . Thus, $(f,g)\in \{(0,4),(3,2),(6,0)\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42799  (f g : ℕ)
  (h₀ : 0 < f ∧ 0 < g)
  (h₁ : 6 * f + 9 * g = 36) :
  (f, g) = (3, 2) ∨ (f, g) = (6, 0) ∨ (f, g) = (0, 4)   :=  by sorry
