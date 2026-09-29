-- Prove2me | Theorems.Thm_lean_workbook_plus_15389
-- name    : lean_workbook_plus_15389
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/714d5253-a640-48fd-862f-cbf5e8291c70
-- statement:
--   Prove that there does not exist $p,q,r\in\mathbb Q$ such that $p+q+r=0$ and $pqr=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15389 (p q r : ℚ) (hp : p + q + r = 0) (hq : p * q * r = 1) : False   :=  by sorry
