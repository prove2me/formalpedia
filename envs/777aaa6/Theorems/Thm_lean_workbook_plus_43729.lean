-- Prove2me | Theorems.Thm_lean_workbook_plus_43729
-- name    : lean_workbook_plus_43729
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/c4e0678d-9c71-4e70-8bdf-9f99886b7b86
-- statement:
--   Prove that if $p\equiv 3\pmod 5$ and $p\equiv 3\pmod 8$, then $40\vert 13p+1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43729 (p : ℕ) (hp1 : p ≡ 3 [ZMOD 5]) (hp2 : p ≡ 3 [ZMOD 8]) : 40 ∣ 13 * p + 1   :=  by sorry
