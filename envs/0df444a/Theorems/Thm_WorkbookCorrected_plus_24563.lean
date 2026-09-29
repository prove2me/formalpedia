-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_24563
-- name    : WorkbookCorrected.plus_24563
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T13:12:25.432128+00:00
-- url     : https://prove2.me/theorems/71bdb664-f4d5-4a03-9295-edf553a75b49
-- title:
--   Classification of a functional equation involving complementary cubes
-- statement:
--   A function $f:\mathbb{R}\to\mathbb{R}$ satisfies
--   \[f(x)+2f(\sqrt[3]{1-x^3})=x^3\qquad(x\in\mathbb{R})\]
--   if and only if $f(x)=\frac23-x^3$ for every real $x$.
--
--   Formalization Note: The real cube root is expressed by the relation y³=1−x³, which uniquely specifies it. Unlike the original formalization, this statement does not omit the cube root or assume a second equation; it proves both necessity and sufficiency of the stated solution.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_24563 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_24563; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_24563 : ∀ (f : ℝ → ℝ),
    (∀ x y : ℝ, y^3 = 1-x^3 → f x + 2*f y = x^3) ↔
    (∀ x : ℝ, f x = 2/3-x^3) := by sorry
