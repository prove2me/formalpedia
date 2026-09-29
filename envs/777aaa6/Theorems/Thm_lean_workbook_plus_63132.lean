-- Prove2me | Theorems.Thm_lean_workbook_plus_63132
-- name    : lean_workbook_plus_63132
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/563c2e19-2277-4ab9-983a-f0afbe23574c
-- statement:
--   Note that $7^2+5^2=74$ . So the left hand side can be written as $\sqrt{74}\left(\frac{7}{\sqrt{74}}\cos x + \frac{5}{\sqrt{74}} \sin x\right)=\sqrt{74}(\sin\phi\cos x + \cos\phi\sin x)$ for some $\phi$ , because the coefficients on the sine and cosine after factoring satisfy the Pythagorean Identity.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63132 :
  ∀ x : ℝ,
    (Real.sqrt 74 * (7 / Real.sqrt 74 * Real.cos x + 5 / Real.sqrt 74 * Real.sin x)) =
    Real.sqrt 74 * (Real.sin (Real.arcsin (5 / Real.sqrt 74)) * Real.cos x + Real.cos (Real.arcsin (5 / Real.sqrt 74)) * Real.sin x)   :=  by sorry
