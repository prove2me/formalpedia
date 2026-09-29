-- Prove2me | Theorems.Thm_mme_asymptotic_sum_inequality
-- name    : mme_asymptotic_sum_inequality
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-28T14:38:48.048236+00:00
-- url     : https://prove2.me/theorems/3e2e472d-9caa-4707-b364-126913cfb868
-- statement:
--   **Schönhage's asymptotic sum inequality (the $\tau$-theorem), specialized to matrix tensors.** Let $K$ be a field and let $\langle n_i,m_i,p_i\rangle$ for $i=1,\dots,k$ be finitely many matrix-multiplication tensors. If the asymptotic rank of their direct sum is at most $r$, then
--
--   $$
--   \sum_{i=1}^{k}\bigl(n_i\,m_i\,p_i\bigr)^{\,\omega^{\mathrm{Str}}_K/3}\;\le\;r,
--   $$
--
--   where $\omega^{\mathrm{Str}}_K$ is the matrix-multiplication exponent in Strassen-preorder form (`matMulExp_strassen K`).
--
--   This is the quantitative engine of every exponent bound in the series: one border-rank construction for a direct sum of matrix tensors, fed through `mme_degenerates_asymptoticRank_le`, immediately yields $\omega<c$ for an explicit rational $c$. The $2.55$ mission instantiates it with $\langle4,1,4\rangle\oplus\langle1,9,1\rangle$ and $r=17$; the Schönhage–Pan–Winograd mission instantiates it with $\langle1,5,22\rangle\oplus\langle11,2,5\rangle\oplus\langle10,11,1\rangle$ and $r=156$.
--
--   **Formalization Note** The direct sum is `TensorObj.bigAdd` of the family $i\mapsto\langle n_i,m_i,p_i\rangle$ indexed by `Fin k`; $r$ is a natural number coerced to $\mathbb{R}$ in the conclusion. No positivity hypotheses are needed on the dimension triples.
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_omega_strassen
universe u
open MME BigOperators

theorem mme_asymptotic_sum_inequality {K : Type u} [Field K] {k : ℕ}
    (n m p : Fin k → ℕ) (r : ℕ)
    (h : tensorAsymptoticRank (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) ≤ r) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) ≤ r := by sorry
