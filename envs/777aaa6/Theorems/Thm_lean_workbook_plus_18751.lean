-- Prove2me | Theorems.Thm_lean_workbook_plus_18751
-- name    : lean_workbook_plus_18751
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/50d03907-828d-4e9f-932e-95f9d8853b3d
-- statement:
--   Given $\cos({\theta}-{\alpha})={p}$ and $\sin({\theta}+{\beta})={q}$, prove that $p^{2}+q^{2}- 2{p}{q}\sin({\alpha}+{\beta}) = \cos^{2}({\alpha}+{\beta})$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18751 (p q θ α β : ℝ) (hp : p = Real.cos (θ - α)) (hq : q = Real.sin (θ + β)) : p^2 + q^2 - 2 * p * q * Real.sin (α + β) = Real.cos (α + β)^2   :=  by sorry
