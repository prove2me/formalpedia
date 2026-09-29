-- Prove2me | Theorems.Thm_WorkbookRestored_plus_63770
-- name    : WorkbookRestored.plus_63770
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:58:24.149346+00:00
-- url     : https://prove2.me/theorems/9a0c8fbc-901f-4733-8378-e785814df47c
-- title:
--   Lean-Workbook Plus 63770: Prime multiplicity of a prime-power binomial coefficient
-- statement:
--   If $p$ is prime and $t$ is a positive integer, then the multiplicity of $p$ in $\binom{p^t}{p^{t-1}}$ is exactly $1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_63770` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/f418eeb8-3817-49b6-b75f-3eddb799a3bf); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_63770; immutable original Prove2Me node f418eeb8-3817-49b6-b75f-3eddb799a3bf

import Mathlib.Data.Nat.Multiplicity
open Nat

theorem WorkbookRestored.plus_63770 (p t : ℕ) (hp : p.Prime) (ht : t ≠ 0)
    : multiplicity p (choose (p^t) (p^(t-1))) = 1   :=  by sorry
