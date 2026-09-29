-- Prove2me | Theorems.Thm_lean_workbook_plus_38916
-- name    : lean_workbook_plus_38916
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/0b2ae5a6-3d34-41f2-aa38-f005ca25f307
-- statement:
--   $2^{5k}\equiv1\pmod5$ \n $2^{5k+1}\equiv2\pmod5$ \n $2^{5k+2}\equiv4\pmod5$ \n $2^{5k+3}\equiv3\pmod5$ \n $2^{5k+4}\equiv1\pmod5$ \n \n $3^{5k}\equiv1\pmod5$ \n $3^{5k+1}\equiv3\pmod5$ \n $3^{5k+2}\equiv4\pmod5$ \n $3^{5k+3}\equiv2\pmod5$ \n $3^{5k+4}\equiv1\pmod5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38916 : ∀ k : ℕ, (2 ^ (5 * k) ≡ 1 [ZMOD 5]) ∧ (2 ^ (5 * k + 1) ≡ 2 [ZMOD 5]) ∧ (2 ^ (5 * k + 2) ≡ 4 [ZMOD 5]) ∧ (2 ^ (5 * k + 3) ≡ 3 [ZMOD 5]) ∧ (2 ^ (5 * k + 4) ≡ 1 [ZMOD 5])   :=  by sorry
