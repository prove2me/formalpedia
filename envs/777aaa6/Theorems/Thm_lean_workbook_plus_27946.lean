-- Prove2me | Theorems.Thm_lean_workbook_plus_27946
-- name    : lean_workbook_plus_27946
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/d44bd445-8b96-4a62-a9c3-35ac58a073ec
-- statement:
--   If $p$ is odd, then $a^p\equiv a\equiv 1\mod p$ implies $p$ divides $a-1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27946 (p a : ℕ) (hp : Odd p) : a^p ≡ a [ZMOD p] ∧ a ≡ 1 [ZMOD p] → p ∣ a - 1   :=  by sorry
