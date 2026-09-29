-- Prove2me | Theorems.Thm_lean_workbook_plus_60981
-- name    : lean_workbook_plus_60981
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/9643fbff-19fa-472d-b556-da316dd9e5c7
-- statement:
--   Prove that for any p>3 ,13 divides $ 10^{2p}-10^p+1 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60981 : ∀ p > 3, 13 ∣ (10^(2 * p) - 10^p + 1)   :=  by sorry
