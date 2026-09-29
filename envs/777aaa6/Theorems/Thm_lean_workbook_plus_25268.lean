-- Prove2me | Theorems.Thm_lean_workbook_plus_25268
-- name    : lean_workbook_plus_25268
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/ec573a3d-2104-4a96-8140-aa4100842283
-- statement:
--   For $0\leq k \leq 6$, $P(|A| = k) = \binom {6} {k} / 2^6$. Then $P(B\subseteq A \vee B\subseteq \overline{A}) = (2^k + 2^{6-k} - 1) / 2^6$. Therefore the required value is $\dfrac {1} {2^{12}}\sum_{k=0}^6 \binom {6} {k} (2^k + 2^{6-k}-1) = \dfrac {1} {2^{12}}(2\cdot 3^6 - 2^6)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25268 :
  (∑ k in Finset.range 7, ((Nat.choose 6 k)/2^6)*(2^k + 2^(6 - k) - 1)) / 2^12 = 153 / 256   :=  by sorry
