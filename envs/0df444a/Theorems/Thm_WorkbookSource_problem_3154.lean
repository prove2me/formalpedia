-- Prove2me | Theorems.Thm_WorkbookSource_problem_3154
-- name    : WorkbookSource.problem_3154
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:38.016463+00:00
-- url     : https://prove2.me/theorems/6a0c0e07-c942-4b16-8b93-8237df0f8095
-- title:
--   A quadratic inequality on a rectangle
-- statement:
--   Suppose $1\le x\le y\le z\le 2$ and denote $u=\frac xz,v=\frac yz\Rightarrow u,v\in\left[\frac 12, 1\right]$ . The inequality becomes $5(u^2+v^2+1)\le 6(u+v+uv)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3154` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3154; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_3154 (u v : ℝ) (hu : 1 / 2 ≤ u ∧ u ≤ 1) (hv : 1 / 2 ≤ v ∧ v ≤ 1) : 5 * (u^2 + v^2 + 1) ≤ 6 * (u + v + u * v)  :=  by sorry
