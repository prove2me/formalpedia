-- Prove2me | Theorems.Thm_lean_workbook_plus_51586
-- name    : lean_workbook_plus_51586
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/0e4dcdc8-0b4b-4f63-ade5-6a640e07049e
-- statement:
--   $S_{2i+1}=ni+2i+1 \equiv i+1$ mod $n+1$ for $i \leq \frac{n-1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51586 (n : ℕ) (i : ℕ) (hi : i ≤ (n-1)/2) : (n*i + 2*i + 1) % (n+1) = (i + 1) % (n+1)   :=  by sorry
