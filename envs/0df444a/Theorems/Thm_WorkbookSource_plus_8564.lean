-- Prove2me | Theorems.Thm_WorkbookSource_plus_8564
-- name    : WorkbookSource.plus_8564
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:10:01.511871+00:00
-- url     : https://prove2.me/theorems/574071a3-5af8-40df-bc85-00803e4f01c2
-- title:
--   Monotonicity of an iterated square-root sequence
-- statement:
--   Given the sequence $\{ a_{n}\}$ where $a_{0}= \frac{1}{3}$ and $a_{n}= \sqrt{\frac{1+a_{n-1}}{2}}$. Show that $\{ a_{n}\}$ is monotonically increasing.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_8564 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_8564; Apache-2.0

import Mathlib

theorem WorkbookSource.plus_8564 (a : ℕ → ℝ) (a0 : a 0 = 1 / 3) (a_rec : ∀ n, a (n + 1) = Real.sqrt ((1 + a n) / 2)) : ∀ n, a n ≤ a (n + 1)   :=  by sorry
