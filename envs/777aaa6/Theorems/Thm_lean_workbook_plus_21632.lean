-- Prove2me | Theorems.Thm_lean_workbook_plus_21632
-- name    : lean_workbook_plus_21632
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/74679eaa-b091-4805-8abc-319af7cba3c7
-- statement:
--   הוכיח כי $f_n=\prod_{k=1}^{\left[\frac{n}{2}\right]}\left(3+2\cos\frac{2\pi k}{n}\right)$ כאשר $n\geq2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21632 (n : ℕ) (hn : 2 ≤ n) : (∏ k in Finset.Icc 1 (n / 2), (3 + 2 * Real.cos (2 * π * k / n))) = (∏ k in Finset.Icc 1 (n / 2), (3 + 2 * Complex.cos (2 * π * k / n)))   :=  by sorry
