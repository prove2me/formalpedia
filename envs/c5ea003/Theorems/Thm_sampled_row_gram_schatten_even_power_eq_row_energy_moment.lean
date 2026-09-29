-- Prove2me | Theorems.Thm_sampled_row_gram_schatten_even_power_eq_row_energy_moment
-- name    : sampled_row_gram_schatten_even_power_eq_row_energy_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T01:53:14.978341+00:00
-- url     : https://prove2.me/theorems/dc01601b-e0dc-46b3-b36b-c4883252e437
-- statement:
--   For $n\ge 1$ and $p>0$, the even power of the sampled row-Gram Schatten scale is exactly the row sampled energy moment:
--   $$\Gamma_{\rm row}^{2n}=\sum_i\left(p^{-2}\sum_j {\bf 1}_{(i,j)\in\Omega}X_{ij}^2\right)^n,$$
--   where
--   $$\Gamma_{\rm row}=\left(\sum_i\left(p^{-1}\sqrt{\sum_j {\bf 1}_{(i,j)\in\Omega}X_{ij}^2}\right)^{2n}\right)^{1/(2n)}.$$
--   This is a formal unpacking of the diagonal row Gram Schatten norm used in the Candes--Recht Khintchine step.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_gram_schatten
open MatrixCompletion
open scoped BigOperators

theorem sampled_row_gram_schatten_even_power_eq_row_energy_moment
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    (sampledRowGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n)
      =
    ∑ i : Fin n1,
      (p⁻¹ ^ 2 *
        (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n := by
  sorry
