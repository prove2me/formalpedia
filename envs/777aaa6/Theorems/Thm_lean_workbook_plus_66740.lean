-- Prove2me | Theorems.Thm_lean_workbook_plus_66740
-- name    : lean_workbook_plus_66740
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/c87130fc-3788-41ae-99db-3d9a880cc080
-- statement:
--   Verify that $\sum_{i=1}^{p-1}{p(p+1)(2p+1) \over 6}=0 \pmod p$ for $p > 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66740 : ℕ) (hp : 3 < p)(hpp : p.Prime) : (∑ i in Finset.range p, (p * (p + 1) * (2 * p + 1) / 6)) % p = 0   :=  by sorry
