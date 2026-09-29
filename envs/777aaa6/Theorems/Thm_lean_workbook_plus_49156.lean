-- Prove2me | Theorems.Thm_lean_workbook_plus_49156
-- name    : lean_workbook_plus_49156
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/3c1e1302-cab7-404b-b80f-ba67c322e218
-- statement:
--   Prove that: \n $1) \binom{n}{m} \binom{n-m}{n-2m}= \binom{n}{2m} \binom{2m}{n}$ ; \n $2) 1!\cdot0+2!\cdot1^2+3!\cdot2^2+...+n!\cdot(n-1)^2=(n+1)!\cdot(n-2)+2 $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49156 : ∀ n m : ℕ, (n.choose m) * (n - m).choose (n - 2 * m) = (n.choose (2 * m)) * (2 * m).choose n   :=  by sorry
