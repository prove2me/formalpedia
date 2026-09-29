-- Prove2me | Theorems.Thm_lean_workbook_plus_33146
-- name    : lean_workbook_plus_33146
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/1a6e1ca8-df30-47e2-9696-db573defcf5c
-- statement:
--   Assume there is some $a$ : \na<sup>2</sup>=(2m+1)<sup>2</sup>+(2n+1)<sup>2</sup> = 4(m<sup>2</sup>+n<sup>2</sup>+m+n)+2 \implies a<sup>2</sup> is divisible by 2
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33146 : ∃ a : ℤ, a^2 = (2*m+1)^2 + (2*n+1)^2 → 2 ∣ a^2   :=  by sorry
