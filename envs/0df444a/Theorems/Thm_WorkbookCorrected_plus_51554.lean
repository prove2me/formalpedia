-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_51554
-- name    : WorkbookCorrected.plus_51554
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T13:17:33.431767+00:00
-- url     : https://prove2.me/theorems/31c71bd5-b14f-47c8-8288-5c1490594b59
-- title:
--   Two solutions of a conjugate cube-root equation
-- statement:
--   For real $x$,
--   \[\sqrt[3]{20+x\sqrt2}+\sqrt[3]{20-x\sqrt2}=4\]
--   holds if and only if $x=14$ or $x=-14$.
--
--   Formalization Note: Real cube roots are specified by their cubing equations. This corrects the natural-number division used in the original fractional powers and includes both directions of the source solution classification.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_51554 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_51554; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_51554 : ∀ (x : ℝ),
    (∃ a b : ℝ, a^3=20+x*Real.sqrt 2 ∧ b^3=20-x*Real.sqrt 2 ∧ a+b=4) ↔
    (x=14 ∨ x= -14) := by sorry
