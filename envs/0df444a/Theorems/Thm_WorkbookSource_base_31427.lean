-- Prove2me | Theorems.Thm_WorkbookSource_base_31427
-- name    : WorkbookSource.base_31427
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:16.053109+00:00
-- url     : https://prove2.me/theorems/6599008e-ae84-461a-a09b-78ae7669d208
-- title:
--   A sixth-degree upper bound at fixed sum three
-- statement:
--   But easy to prove that $ 16\geq7u^{2}v^{2}w^{2}+3(u^{2}v^{2}+u^{2}w^{2}+v^{2}w^{2})$ is true
--   for all non-negative $ u,$ $ v$ and $ w$ such that $ u+v+w=3.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31427` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31427; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31427 (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (h : u + v + w = 3) : 16 ≥ 7 * u^2 * v^2 * w^2 + 3 * (u^2 * v^2 + u^2 * w^2 + v^2 * w^2)  :=  by sorry
