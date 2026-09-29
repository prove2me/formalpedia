-- Prove2me | Theorems.Thm_lean_workbook_plus_37865
-- name    : lean_workbook_plus_37865
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/51b3b759-46ab-41e8-86fc-8c4cbd61a3af
-- statement:
--   Let $a,b$ be two integers. Prove that \n\na) $13 \mid 2a+3b$ if and only if $13 \mid 2b-3a$ ; \nb) If $13 \mid a^2+b^2$ then $13 \mid (2a+3b)(2b+3a)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37865 (a b : ℤ) : (13 ∣ (2 * a + 3 * b)) ↔ (13 ∣ (2 * b - 3 * a))   :=  by sorry
