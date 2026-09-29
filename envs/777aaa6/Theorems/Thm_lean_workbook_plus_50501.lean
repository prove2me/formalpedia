-- Prove2me | Theorems.Thm_lean_workbook_plus_50501
-- name    : lean_workbook_plus_50501
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/ee5004c6-a136-476b-94d5-843c9832bf70
-- statement:
--   For $a,b,c\\ge0$ prove that \n\n $a^{4}+b^{4}+c^{4}\\geq a^{3}b+b^{3}c+c^{3}a$ \n\n or equivalently (according to <http://www.mathlinks.ro/Forum/viewtopic.php?t=103773>) \n\n $[4,0,0]\\ge[3,1,0]$ \n\n Well, that is easy. Just sum AM-GM of the form \n\n $\frac{a^{4}+a^{4}+a^{4}+b^{4}}{4}\\geq a^{3}b$ \n\n implies desired result. Equality occurs iff $a=b=c$ . \n\n Note that our inequality can be valid for all reals.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50501  (a b c : ℝ) :
  a^4 + b^4 + c^4 ≥ a^3 * b + b^3 * c + c^3 * a   :=  by sorry
