-- Prove2me | Theorems.Thm_lean_workbook_plus_36759
-- name    : lean_workbook_plus_36759
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/4dc318c2-653d-48c6-85d8-5895681ce698
-- statement:
--   Ha! Jacobstal's Identity. Do you want a full solution or just some hints? If the latter, then, for starters, notice that for any $m, n$ , such that $ \left(\frac{m}{p}\right) = \left(\frac{n}{p}\right) $ ; $ \displaystyle \sum_{i=1}^{p-1} \left( \frac{i (i^2 - m)}{p} \right) = \displaystyle \sum_{i=1}^{p-1} \left( \frac{i (i^2 - n)}{p} \right)$ . Then add up, over all $\frac{p-1}{2}$ residues and non-residues and use symmetry.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36759 (p m n : ℕ) (hp : p.Prime) (h0 : p > 2) (h1 : (m : ZMod p) = n) : (∑ i in Finset.range p, ((i : ZMod p) * (i ^ 2 - m) : ZMod p)) = (∑ i in Finset.range p, ((i : ZMod p) * (i ^ 2 - n) : ZMod p))   :=  by sorry
