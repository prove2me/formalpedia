-- Prove2me | Theorems.Thm_lean_workbook_plus_49946
-- name    : lean_workbook_plus_49946
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/02ec2da7-507c-4f96-bd7a-098406c628b4
-- statement:
--   Prove that $2^{100} \mid \prod_{n=101}^{200} n$ , but $2^{101} \nmid \prod_{n=101}^{200} n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49946 : 2 ^ 100 ∣ ∏ n in Finset.Icc 101 200, n   :=  by sorry
