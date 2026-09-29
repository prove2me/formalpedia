-- Prove2me | Theorems.Thm_lean_workbook_plus_33164
-- name    : lean_workbook_plus_33164
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/26b9a448-a92b-45e6-a046-bdbf266c908a
-- statement:
--   If $ x\in [0,\pi]$ then show that : $ (1+\sin x)\cdot\cos^2 x\le \frac{32}{27}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33164 : ∀ x ∈ Set.Icc 0 Real.pi, (1 + Real.sin x) * (Real.cos x)^2 ≤ 32/27   :=  by sorry
