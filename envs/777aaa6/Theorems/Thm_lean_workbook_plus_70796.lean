-- Prove2me | Theorems.Thm_lean_workbook_plus_70796
-- name    : lean_workbook_plus_70796
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/39ac8849-a284-4b2b-bdb2-8ddc720827b9
-- statement:
--   Show that the series $\sum_{k=1}^{\infty} \frac{\sin(\sqrt{k})}{k^2}$ converges using the comparison test with the convergent $p$-series $\sum_{k=1}^{\infty} \frac{1}{k^2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70796 : ∀ k : ℕ, ‖sin (Real.sqrt k) / k ^ 2‖ ≤ 1 / k ^ 2   :=  by sorry
