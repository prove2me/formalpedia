-- Prove2me | Theorems.Thm_lean_workbook_plus_38947
-- name    : lean_workbook_plus_38947
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/d5a98f73-fddb-4593-a73a-dc16f5a4ed84
-- statement:
--   If $p$ is a prime number of the form $p = 4k+1$ , show that $\sum_{a=1}^{p-1} a \left ( \frac ap \right) = 0$ Where $\left ( \frac ap \right) $ denotes the the moulo $p$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38947 (p : ℕ) (hp : p.Prime) (h : p = 4 * k + 1) : ∑ a in Finset.range p, a * (a / p) = 0   :=  by sorry
