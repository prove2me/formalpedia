-- Prove2me | Theorems.Thm_lean_workbook_plus_34642
-- name    : lean_workbook_plus_34642
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/0207afd8-3c76-45a1-b3a1-0d6f88a02f0a
-- statement:
--   Prooving the converse: \n $\begin{array}{l}(a + b)^2 = {a^2} + 2ab + {b^2} \Rightarrow (a + b)(a + b) = {a^2} + 2ab + {b^2} \\\Rightarrow {a^2} + ab + ba + {b^2} = {a^2} + 2ab + {b^2} \Rightarrow ab + ba = 2ab = ab + ab \Rightarrow ab = ba\end{array}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34642  (a b : ℝ)
  (h₀ : (a + b)^2 = a^2 + 2 * a * b + b^2) :
  a * b = b * a   :=  by sorry
