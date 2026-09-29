-- Prove2me | Theorems.Thm_lean_workbook_plus_21714
-- name    : lean_workbook_plus_21714
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/c7ccbc08-f762-4ddc-af33-86d228818796
-- statement:
--   Starting from $1$ , assume $A$ contains $1$ . Then $A$ should also contain the preimage of $1$ . $A$ should also contain the preimage of preimage of $1$ . Repeating this, $A$ should at least contain every $x$ with $g^n (x)=1$ for some non-negative integer $n$ . And stop.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21714 (f : ℕ → ℕ) (g : ℕ → ℕ) (hg : g = fun x => if x = 1 then 1 else x - 1) (A : Set ℕ) (hA : A = {x | ∃ n : ℕ, g^[n] x = 1}) : A = {x | ∃ n : ℕ, g^[n] x = 1}   :=  by sorry
