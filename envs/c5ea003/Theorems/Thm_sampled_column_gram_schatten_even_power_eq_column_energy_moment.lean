-- Prove2me | Theorems.Thm_sampled_column_gram_schatten_even_power_eq_column_energy_moment
-- name    : sampled_column_gram_schatten_even_power_eq_column_energy_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T01:53:41.909413+00:00
-- url     : https://prove2.me/theorems/2ae065a8-a64e-4830-bb04-c691e3c44a1a
-- statement:
--   For $n\ge 1$ and $p>0$, the even power of the sampled column-Gram Schatten scale is exactly the column sampled energy moment:
--   $$\Gamma_{\rm col}^{2n}=\sum_j\left(p^{-2}\sum_i {\bf 1}_{(i,j)\in\Omega}X_{ij}^2\right)^n,$$
--   where
--   $$\Gamma_{\rm col}=\left(\sum_j\left(p^{-1}\sqrt{\sum_i {\bf 1}_{(i,j)\in\Omega}X_{ij}^2}\right)^{2n}\right)^{1/(2n)}.$$
--   This is a formal unpacking of the diagonal column Gram Schatten norm used in the Candes--Recht Khintchine step.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_gram_schatten
open MatrixCompletion
open scoped BigOperators

theorem sampled_column_gram_schatten_even_power_eq_column_energy_moment
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    (sampledColumnGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n)
      =
    ∑ j : Fin n2,
      (p⁻¹ ^ 2 *
        (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n := by
  sorry
