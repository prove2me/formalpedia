-- Prove2me | Theorems.Thm_lean_workbook_plus_57951
-- name    : lean_workbook_plus_57951
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/6c03fc45-3fd5-4840-aaaa-99ce7ac99b6a
-- statement:
--   1) $1+\frac12 \left( 1+\frac14+\left( \frac14 \right)^2+ \dots \right)+\frac{1}{16} \left( 1+\frac{1}{16}+\left( \frac{1}{16} \right)^2+ \dots \right)=1+\frac12 \cdot \frac43+\frac{1}{16} \cdot \frac{16}{15}=1+\frac23+\frac{1}{15}=\boxed{\frac{26}{15}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57951 :
  1 + (1 / 2) * (∑' k : ℕ, (1 / 4)^k) + (1 / 16) * (∑' k : ℕ, (1 / 16)^k) = 26 / 15   :=  by sorry
