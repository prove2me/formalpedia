-- Prove2me | Theorems.Thm_lean_workbook_plus_7090
-- name    : lean_workbook_plus_7090
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/0b594001-dce7-4017-a313-251a6cc8dc33
-- statement:
--   For positives $a$ , $b$ and $c$ we obtain\n\n$\sum_{cyc}a\sum_{cyc}\frac{1}{1+a^2}\geq\sum_{cyc}\frac{a^2}{1+a^2}\sum_{cyc}\frac{1}{a}\Leftrightarrow\sum_{cyc}a\sum_{cyc}\frac{1}{1+a^2}\geq\left(3-\sum_{cyc}\frac{1}{1+a^2}\right)\sum_{cyc}\frac{1}{a}\Leftrightarrow$\n\n$\Leftrightarrow\sum_{cyc}\left(a+\frac{1}{a}\right)\sum_{cyc}\frac{1}{1+a^2}\geq3\sum_{cyc}\frac{1}{a}\Leftrightarrow\sum_{cyc}\left(\frac{1+a^2}{a(1+b^2)}+\frac{1+a^2}{a(1+c^2)}\right)\geq2\sum_{cyc}\frac{1}{a}\Leftrightarrow$\n\n$\Leftrightarrow\sum_{cyc}\left(\frac{1+a^2}{a(1+b^2)}+\frac{1+b^2}{b(1+a^2)}-\frac{1}{a}-\frac{1}{b}\right)\geq\Leftrightarrow\sum_{cyc}(a^2-b^2)\left(\frac{1}{a(1+b^2)}-\frac{1}{b(1+a^2)}\right)\geq0\Leftrightarrow$\n\n$\Leftrightarrow\sum_{cyc}\frac{(a-b)^2(a+b)(ab-1)}{ab(1+a^2)(1+b^2)}\geq0$ . Done!
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7090 :
  ∀ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c →
  (a + b + c) * (1 / (1 + a^2) + 1 / (1 + b^2) + 1 / (1 + c^2)) ≥
    (a^2 / (1 + a^2) + b^2 / (1 + b^2) + c^2 / (1 + c^2)) * (1 / a + 1 / b + 1 / c)   :=  by sorry
