-- Prove2me | Theorems.Thm_lean_workbook_plus_20146
-- name    : lean_workbook_plus_20146
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/1e77998e-195e-4a63-b826-637d6294abff
-- statement:
--   Consider a set $A$ of ' $n$ ' distinct numbers.\nLet us calculate the total number of subsets of the set.\nNow the cardinality of the subset ranges from $0$ to $n$ \nChoose a r element subset. Total number of $r-$ element subset= $n\choose r$ \nThus, total number of subsets is $\sum_{r=0}^{n}{n\choose r}$\nFor each element of $A$ , it can either be in a subset or not $=2$ choices\nFor $\;n\;$ elements $=2^n$ choices $\implies 2^n$ subsets
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20146 ∑ k in Finset.range (n+1), (n.choose k) = 2^n   :=  by sorry
