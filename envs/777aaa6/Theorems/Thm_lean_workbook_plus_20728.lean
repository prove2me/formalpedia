-- Prove2me | Theorems.Thm_lean_workbook_plus_20728
-- name    : lean_workbook_plus_20728
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/26ff7405-84c2-4826-bd60-751b0c4098c3
-- statement:
--   Thinking through this, weighing anything up to $\left\lfloor\frac{3^k}{2}\right\rfloor$ takes $k$ weights. $\lceil\log_3(2\cdot2009)\rceil=\boxed{8}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20728 (k : ℕ) (h₁ : 0 < k) (h₂ : 2 * 2009 ≤ 3 ^ k) : k >= 8   :=  by sorry
