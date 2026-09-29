-- Prove2me | Theorems.Thm_lean_workbook_plus_29816
-- name    : lean_workbook_plus_29816
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/f407ae42-e1ff-4d28-8eb7-f4603294f3a3
-- statement:
--   a) Let $n$ be the number of players and $k$ the number of minutes played by each player. Then $k\cdot n=90\cdot11$ since both sides is equal to the total number of minutes played. Since $k<60$ , $60n<90\cdot 11\Longleftrightarrow n\geq 17$ . Since $n\mid 90\cdot11$ , $n\geq 18$ . If $n=18$ each player has to play for $55$ minutes. It is possible with $18$ players. Label the players $p_0,p_1,...,p_{17}$ . We start with the players $p_0,p_1,...,p_{10}$ on the field. For each $i\in\{0,1,...,16\}$ $p_i$ is substituted with $p_{i+11}$ (indices are considered modulo $18$ ) after $5(i+1)$ minutes have been played. Then each player plays exactly $55$ minutes, so the minimum number of players required is $18$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29816  (n k : ℕ)
  (h₀ : 0 < n ∧ 0 < k)
  (h₁ : k < 60)
  (h₂ : (n * k) = 90 * 11) :
  18 ≤ n   :=  by sorry
