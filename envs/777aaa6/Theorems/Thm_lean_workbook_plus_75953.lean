-- Prove2me | Theorems.Thm_lean_workbook_plus_75953
-- name    : lean_workbook_plus_75953
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/8d464474-7736-4e58-9b91-19e1bc74f85d
-- statement:
--   Given three real numbers $p$ , $q$ , and $r$ where $0<p,q,r<1$ . Show that $pq+qr+rp-2pqr<1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75953 (p q r : ℝ) (hp : 0 < p ∧ p < 1) (hq : 0 < q ∧ q < 1) (hr : 0 < r ∧ r < 1) : p*q + q*r + r*p - 2*p*q*r < 1   :=  by sorry
