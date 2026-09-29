-- Prove2me | Theorems.Thm_WorkbookSource_problem_837
-- name    : WorkbookSource.problem_837
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:12:10.902559+00:00
-- url     : https://prove2.me/theorems/4d495fdd-9e3d-4862-9014-73755ba4caae
-- title:
--   A symmetric polynomial substitution identity
-- statement:
--   Prove that $xz=p(q-r)+r^2$ where $p=a^2+b^2+c^2$, $q=ab+bc+ca$, $r=(b-a)(b-c)$, $x=a^2+2bc$, $y=b^2+2ca$, and $z=c^2+2ab$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_837` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_837; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_837 :∀ a b c x y z p q r : ℝ,  p = a^2 + b^2 + c^2 ∧ q = a * b + b * c + c * a ∧ r = (b - a) * (b - c) ∧ x = a^2 + 2 * b * c ∧ y = b^2 + 2 * c * a ∧ z = c^2 + 2 * a * b → x * z = p * (q - r) + r^2  :=  by sorry
