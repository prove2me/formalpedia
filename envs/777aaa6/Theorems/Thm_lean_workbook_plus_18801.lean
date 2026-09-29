-- Prove2me | Theorems.Thm_lean_workbook_plus_18801
-- name    : lean_workbook_plus_18801
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d27a5746-7888-4c06-9f28-3cc21df23001
-- statement:
--   Given $q^2\ge pr, r^2 \ge pq, \{p,q,r\}\in R^{+}$, prove that $\sqrt{qr}\ge p$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18801 (p q r : ℝ) (h : {p,q,r} ⊆ Set.Ioi 0) (hpqr : p * q * r = 1) (hq2 : q^2 ≥ p * r) (hr2 : r^2 ≥ p * q) : √(q * r) ≥ p   :=  by sorry
