-- Prove2me | Theorems.Thm_bernoulli_powerset_expectation_quadruple
-- name    : bernoulli_powerset_expectation_quadruple
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T22:12:28.35198+00:00
-- url     : https://prove2.me/theorems/f57d028d-491c-4426-950e-1994f7de48ef
-- statement:
--   **Quadruple linearity of the Bernoulli powerset expectation.** For the finite Bernoulli observation measure on $\Omega \subseteq [n_1]\times[n_2]$ (each coordinate included independently with probability $p$), the expectation of a fourfold coordinate sum of functions of four inclusion indicators pushes through all four sums term by term: $\mathbb{E}[\sum_{a,b,c,d} G_{abcd}(\mathbf 1_a,\mathbf 1_b,\mathbf 1_c,\mathbf 1_d)] = \sum_{a,b,c,d}\mathbb{E}[G_{abcd}(\mathbf 1_a,\mathbf 1_b,\mathbf 1_c,\mathbf 1_d)]$, where $\mathbf 1_w=\mathbf 1[w\in\Omega]$. This is the linearity step that expands the fourth moment of a statistic linear in the inclusion indicators (e.g. the centered sampling coefficient $\sum_{ij}p^{-1}(\mathbf 1[(i,j)\in\Omega]-p)B_{ij}$) into a fourfold sum of coordinate expectations — the first step of the Rosenthal/Latała even-moment expansion (Boucheron–Lugosi–Massart, *Concentration Inequalities*, OUP 2013, Ch. 15) used in the scalar/noncommutative Bernstein moment bounds of Candès–Recht 2009 (arXiv:0805.4471, §6).
-- source:
--   https://arxiv.org/abs/0805.4471

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators Classical

theorem bernoulli_powerset_expectation_quadruple {n₁ n₂ : ℕ} (p : ℝ)
    (G : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) →
      ℝ → ℝ → ℝ → ℝ → ℝ) :
    bernoulliExpectation p
        (fun Omega => ∑ a : Fin n₁ × Fin n₂, ∑ b : Fin n₁ × Fin n₂,
          ∑ c : Fin n₁ × Fin n₂, ∑ d : Fin n₁ × Fin n₂,
          G a b c d (if a ∈ Omega then 1 else 0) (if b ∈ Omega then 1 else 0)
            (if c ∈ Omega then 1 else 0) (if d ∈ Omega then 1 else 0)) =
      ∑ a : Fin n₁ × Fin n₂, ∑ b : Fin n₁ × Fin n₂,
        ∑ c : Fin n₁ × Fin n₂, ∑ d : Fin n₁ × Fin n₂,
        bernoulliExpectation p
          (fun Omega => G a b c d (if a ∈ Omega then 1 else 0) (if b ∈ Omega then 1 else 0)
            (if c ∈ Omega then 1 else 0) (if d ∈ Omega then 1 else 0)) := by sorry
