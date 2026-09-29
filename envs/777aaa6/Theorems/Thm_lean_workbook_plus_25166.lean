-- Prove2me | Theorems.Thm_lean_workbook_plus_25166
-- name    : lean_workbook_plus_25166
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/80a0ec78-a4a0-438b-9ca7-ca6a5bafbb99
-- statement:
--   Note that each possible difference must be in the form $2^a - 2^b$ . Now we take cases on $a$ . If $a=1$ , there are $1 \cdot 2^1 - (2^1-1)$ ways. If $a=2$ , then there are $2 \cdot 2^2 - (2^2-1)$ ways, and so on. The answer is $(1 \cdot 2^1 + 2 \cdot 2^2 + 3 \cdot 2^3 + \ldots + 10 \cdot 2^{10}) - (2^1+2^2+2^3 + \ldots + 2^{10} - 10) \equiv 16398 \equiv \boxed{398} \pmod {1000}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25166 :
  ∑ k in (Finset.Icc 1 10), ((k + 1) * 2^(k + 1) - 2^(k + 1) + 1) ≡ 398 [MOD 1000]   :=  by sorry
