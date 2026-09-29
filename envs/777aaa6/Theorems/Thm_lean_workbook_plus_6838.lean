-- Prove2me | Theorems.Thm_lean_workbook_plus_6838
-- name    : lean_workbook_plus_6838
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/caedb359-b09e-4de8-b5d5-cc6b54148726
-- statement:
--   $n^{p-1}= (n^{2})^{\frac{p-1}{2}}\equiv (-1)^{\frac{p-1}{2}}(mod p)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6838 {p n : ℕ} (hp : p.Prime) (hpo : Odd p) (h : ((n:ℤ)^(p-1) ≡ (-1:ℤ)^((p-1)/2) [ZMOD p])) : n^(p-1) ≡ (-1)^((p-1)/2) [ZMOD p]   :=  by sorry
