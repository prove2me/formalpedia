-- Prove2me | Theorems.Thm_lean_workbook_plus_48724
-- name    : lean_workbook_plus_48724
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/68e2e77b-e850-492c-98b3-aac6def62559
-- statement:
--   $3^{16}\equiv 1\pmod{64}$ and so we just have to check for $n\in[0,63]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48724 :
  ∀ n ∈ Finset.range 64, 3^16 ≡ 1 [ZMOD 64]   :=  by sorry
