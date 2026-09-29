-- Prove2me | Theorems.Thm_WorkbookSource_problem_13238
-- name    : WorkbookSource.problem_13238
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:11:25.486121+00:00
-- url     : https://prove2.me/theorems/71be36b6-72ea-47a5-82e3-8d68d4e7715c
-- title:
--   Squares can hide distinct residues modulo three
-- statement:
--   In 6.2, when considering the congruence modulo 3, show that $x^2 \equiv y^2 \pmod{3}$ does not imply $x \equiv y \pmod{3}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13238` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13238; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_13238 : ∃ x y : ℤ, (x^2 ≡ y^2 [ZMOD 3]) ∧ ¬ (x ≡ y [ZMOD 3])  :=  by sorry
