-- Prove2me | Theorems.Thm_lean_workbook_plus_77316
-- name    : lean_workbook_plus_77316
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/4773300f-5b20-4fa4-9aee-c1980a043c9a
-- statement:
--   Let $ a > 2$ , and $ \{ {a_n}\}$ $ \left( {{\rm{n}} = {\rm{1}},{\rm{2}} \ldots .} \right)$ be a sequence given by \n $ {a_0} = 1,{a_1} = a,{a_{n + 1}} = \left( {\frac{{a_n^2}}{{a_{n - 1}^2}} - 2} \right){a_n}$ . \nProve that $ \forall k \in N$ we have \n $ \frac{1}{{{a_0}}} + \frac{1}{{{a_1}}} + \ldots + \frac{1}{{{a_k}}} < \frac{1}{2}\left( {2 + a - \sqrt {{a^2} - 4} } \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77316  (a : ℝ)
  (a0 : a > 2)
  (a_n : ℕ → ℝ)
  (h0 : a_n 0 = 1)
  (h1 : a_n 1 = a)
  (h_rec : ∀ n, a_n (n + 1) = (a_n n ^ 2 / a_n (n - 1) ^ 2 - 2) * a_n n) :
  ∀ k, ∑ i in Finset.range (k + 1), (1 / a_n i) < (1 / 2) * (2 + a - Real.sqrt (a ^ 2 - 4))   :=  by sorry
