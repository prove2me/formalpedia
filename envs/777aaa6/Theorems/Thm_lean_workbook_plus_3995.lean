-- Prove2me | Theorems.Thm_lean_workbook_plus_3995
-- name    : lean_workbook_plus_3995
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/7dee68f8-46dc-4891-b246-4825dffa6d13
-- statement:
--   Note that $\log_{10}2\approx0.301$ , so $2^{100}\approx\left(10^{0.301}\right)^{100}=10^{(0.301)(100)}=10^{30.1}$ , and thus $10^{30}<10^{30.1}\approx2^{100}<10^{31}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3995 :
  (10:ℝ)^30 < 2^100 ∧ 2^100 < (10:ℝ)^31   :=  by sorry
