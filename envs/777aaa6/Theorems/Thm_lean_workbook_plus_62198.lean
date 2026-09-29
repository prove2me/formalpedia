-- Prove2me | Theorems.Thm_lean_workbook_plus_62198
-- name    : lean_workbook_plus_62198
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/1d4a3c09-8e2c-4d7a-9433-1717f6f36e9d
-- statement:
--   For $ {\pi\over 2}\leqslant x\leqslant {3\pi\over 2}$ you have $ \arcsin(\sin x)=\pi-x$ . Hence you need to reduce real $ x$ to interval $ \left(-{\pi\over 2},{3\pi\over 2}\right)$ and you can do it by using the argument $ z=x-2\pi\left[{x\over 2\pi}+{1\over 4}\right]$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62198 ∀ x, (π/2 ≤ x ∧ x ≤ 3*π/2) → Real.arcsin (Real.sin x) = π - x   :=  by sorry
