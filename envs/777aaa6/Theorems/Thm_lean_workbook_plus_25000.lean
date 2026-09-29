-- Prove2me | Theorems.Thm_lean_workbook_plus_25000
-- name    : lean_workbook_plus_25000
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/40c2dacc-54ee-47b7-808a-bc3e7ff768f2
-- statement:
--   Prove that if $x^6\equiv 1\pmod{p^k}$, then $\text{ord}_{p^k}(x)\mid 6$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25000 (p k : ℕ) (x : Units (ZMod (p^k))) (hx : x^6 = 1) :
    orderOf x ∣ 6   :=  by sorry
