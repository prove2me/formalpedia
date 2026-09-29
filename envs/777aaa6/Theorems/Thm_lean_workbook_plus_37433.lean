-- Prove2me | Theorems.Thm_lean_workbook_plus_37433
-- name    : lean_workbook_plus_37433
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/97bcb53b-ef1e-4e6a-bd56-dd3efafe54e8
-- statement:
--   If $p$ is a prime so that $p\equiv 1 mod 4$ , then $x^2\equiv 1 \mod p$ if and only if $x\equiv \pm 1 \mod p$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37433 (p : ℕ) (hp : p.Prime) (hp1 : p ≡ 1 [ZMOD 4]) : (∃ x : ZMod p, x^2 = 1) ↔ ∃ x : ZMod p, x = 1 ∨ x = -1   :=  by sorry
