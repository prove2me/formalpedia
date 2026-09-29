-- Prove2me | Theorems.Thm_bernoulli_powerset_expectation_double
-- name    : bernoulli_powerset_expectation_double
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T21:05:21.876219+00:00
-- url     : https://prove2.me/theorems/726fbda4-fa98-4a02-b4e2-6d36f7bda935
-- statement:
--   **Double linearity of the Bernoulli powerset expectation.** The expectation of a double coordinate sum of functions of two inclusion indicators pushes through both sums term-by-term: $$\mathbb{E}\Big[\sum_w\sum_{w'} G_{w,w'}(\mathbf{1}[w\in\Omega],\mathbf{1}[w'\in\Omega])\Big] = \sum_w\sum_{w'}\mathbb{E}\big[G_{w,w'}(\mathbf{1}[w\in\Omega],\mathbf{1}[w'\in\Omega])\big].$$ This is the form used to expand the second moment (variance) of a statistic linear in the inclusion indicators into a double sum of pair-coordinate expectations.
-- source:
--   Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Ch. 15; Candès–Recht 2009, arXiv:0805.4471, §6 (centered sampling operator p⁻¹(P_Ω − p)).

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators

theorem bernoulli_powerset_expectation_double {n₁ n₂ : ℕ} (p : ℝ)
    (G : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → ℝ → ℝ → ℝ) :
    bernoulliExpectation p
        (fun Omega => ∑ w : Fin n₁ × Fin n₂, ∑ w' : Fin n₁ × Fin n₂,
          G w w' (if w ∈ Omega then 1 else 0) (if w' ∈ Omega then 1 else 0)) =
      ∑ w : Fin n₁ × Fin n₂, ∑ w' : Fin n₁ × Fin n₂,
        bernoulliExpectation p
          (fun Omega => G w w' (if w ∈ Omega then 1 else 0) (if w' ∈ Omega then 1 else 0)) := by sorry
