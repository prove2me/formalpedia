-- Prove2me | Theorems.Thm_lean_workbook_plus_41095
-- name    : lean_workbook_plus_41095
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/3276e9c5-cbdf-4c14-b55b-afe654198a71
-- statement:
--   $ \frac {\sin A \sin B \sin C}{\sin A + \sin B + \sin C}\geq 3\cdot \frac {\cos A \cos B \cos C}{\cos A + \cos B + \cos C}$ $ \Longleftrightarrow$ $ \prod\tan A\ge \frac {3s}{R + r}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41095 : ∀ {A B C : ℝ}, A ∈ Set.Ioc 0 Real.pi ∧ B ∈ Set.Ioc 0 Real.pi ∧ C ∈ Set.Ioc 0 Real.pi ∧ A + B + C = Real.pi → (Real.sin A * Real.sin B * Real.sin C) / (Real.sin A + Real.sin B + Real.sin C) ≥ 3 * (Real.cos A * Real.cos B * Real.cos C) / (Real.cos A + Real.cos B + Real.cos C) ↔ Real.tan A * Real.tan B * Real.tan C ≥ 3 * (Real.pi * Real.sin A * Real.sin B * Real.sin C) / (Real.pi * Real.cos A * Real.cos B * Real.cos C)   :=  by sorry
