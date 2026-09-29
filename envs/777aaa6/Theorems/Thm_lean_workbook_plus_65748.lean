-- Prove2me | Theorems.Thm_lean_workbook_plus_65748
-- name    : lean_workbook_plus_65748
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/5efacbaa-5685-42fe-936f-6a435f58a8e9
-- statement:
--   Let $p$ be an odd prime. Prove that for all positive integers $n<\frac{p-1}{2}$ , \n $1^{2n}+2^{2n}+\cdots+\left(\frac{p-1}{2}\right)^{2n}\equiv 0\pmod{p}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65748 (p : ℕ) (hp : p.Prime) (hp1 : Odd p) (n : ℕ) (hn : n < (p-1)/2) : (∑ i in Finset.range ((p-1)/2 + 1), (i ^ (2 * n)) % p) = 0   :=  by sorry
