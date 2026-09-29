-- Prove2me | Theorems.Thm_lean_workbook_plus_24600
-- name    : lean_workbook_plus_24600
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/bd5f6a95-d2dc-41bc-a519-896b43d1d2bd
-- statement:
--   We see $7^4=2401 \equiv 1 \pmod{100}$ . So $(7^4)^{502} \equiv 1 \pmod{100} \rightarrow (7^4)^{502}.7^2 \equiv 49 \pmod{100}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24600 :
  (7^4)^502 * 7^2 ≡ 49 [MOD 100]   :=  by sorry
