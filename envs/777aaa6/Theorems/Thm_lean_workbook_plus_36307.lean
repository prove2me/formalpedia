-- Prove2me | Theorems.Thm_lean_workbook_plus_36307
-- name    : lean_workbook_plus_36307
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/4fcadc57-7189-4872-a25e-87913d56caca
-- statement:
--   $\dfrac{1}{\sqrt{n}}>2(\sqrt{n+1}-\sqrt{n})$ (directly or using the mean value theorem for $f(x)=\sqrt{x}$ and the interval $[n,n+1])$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36307 (n : ℕ) (hn : 0 < n) :
  (1 / Real.sqrt n) > 2 * (Real.sqrt (n + 1) - Real.sqrt n)   :=  by sorry
