-- Prove2me | Theorems.Thm_lean_workbook_plus_15837
-- name    : lean_workbook_plus_15837
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/6a1bb00a-8ba6-4361-bc5f-efbfcc70bee5
-- statement:
--   Anyway, $p\mid qr+q+r\to p\mid pq+qr+rp+p+q+r$ In the same way, $q\mid pq+qr+rp+p+q+r$ and $r\mid pq+qr+rp+p+q+r$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15837 (p q r : ℕ) : p ∣ q * r + q + r → p ∣ p * q + q * r + r * p + p + q + r   :=  by sorry
