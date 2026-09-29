-- Prove2me | Theorems.Thm_lean_workbook_plus_78622
-- name    : lean_workbook_plus_78622
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/45ccf3b4-afe0-49b0-83a2-a85f354895fa
-- statement:
--   Prove that:\n1/ $\sin(\frac{\pi}{2m})\sin(\frac{2\pi}{2m})\sin(3\frac{\pi}{2m})...sin(\frac{(m-1)\pi}{2m})=\frac{\sqrt{m}}{2^{m-1}}$ \n2/ $\sin(\frac{\pi}{4m})\sin(\frac{3\pi}{4m})\sin(\frac{5\pi}{4m})...sin(\frac{(2m-1)\pi}{4m})=\frac{\sqrt{2}}{2^{m-1}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78622 : ∀ m : ℕ, (∏ k in Finset.range m, sin ((k + 1) * π / (2 * m))) = √m / 2 ^ (m - 1)   :=  by sorry
