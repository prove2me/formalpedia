-- Prove2me | Theorems.Thm_WorkbookRestored_plus_34718
-- name    : WorkbookRestored.plus_34718
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:34:19.458833+00:00
-- url     : https://prove2.me/theorems/03a6b5a5-f390-4538-801c-2a764fb31481
-- title:
--   Lean-Workbook Plus 34718: Trigonometric identity
-- statement:
--   **Lean-Workbook Plus 34718: Fourth power of the imaginary unit**
--
--   For complex $q,e$ with $q=i$ and $e=4$, $q^e=1$. The formal exponent is complex, and at the integer value four it agrees with the usual fourth power.
--
--   Source: Lean-Workbook row `lean_workbook_plus_34718` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/acc4dae6-7b29-42c4-9f04-49279b9670d4); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_34718; immutable original Prove2Me node acc4dae6-7b29-42c4-9f04-49279b9670d4

import Mathlib.Analysis.SpecialFunctions.Pow.Complex

theorem WorkbookRestored.plus_34718  (q e : ℂ)
  (h₀ : q = Complex.I)
  (h₁ : e = 4) :
  q^e = 1   :=  by sorry
