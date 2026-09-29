-- Prove2me | Theorems.Thm_talagrand_bernoulli_sSup_log_tail_from_finite_max
-- name    : talagrand_bernoulli_sSup_log_tail_from_finite_max
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-29T17:07:58.856578+00:00
-- url     : https://prove2.me/theorems/a62b05bf-3558-4633-aad9-72f553d85125
-- statement:
--   Formal bridge from the finite-class maximum theorem to the arbitrary-index $\operatorname{sSup}$ formulation of Appendix 9.1 used in the matrix-completion mission.
--
--   The parent theorem allows an arbitrary index type $\iota$ and defines
--   $$
--   Z(\Omega)=\sup_{a\in\iota}\sum_{i,j}\bigl(1_{(i,j)\in\Omega}-p\bigr)c_a(i,j),
--   \qquad p={m\over n_1n_2}.
--   $$
--   The finite-max theorem only treats finite nonempty symmetric classes.  This bridge says that finite-class concentration is enough for the arbitrary $\operatorname{sSup}$ statement: since the Bernoulli observation set $\Omega$ has only finitely many possible values, one can approximate the suprema simultaneously on all sample points by a finite set of indices, close that finite set under the supplied symmetry $c_{a'}=-c_a$, apply the finite-max theorem, and pass to the limit.
--
--   The empty-index case is degenerate: the supremum set is empty at every sample point, so $Z$ is constant and the concentration event is automatic.  No matrix-completion geometry is involved in this node; it is purely the formal finite-state approximation step needed because the Lean theorem is stated with arbitrary $\iota$ rather than the countable class appearing in the paper.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MatrixCompletion
open scoped Classical BigOperators

theorem talagrand_bernoulli_sSup_log_tail_from_finite_max
    (hfinite :
      ∃ K : ℝ, 0 < K ∧
        ∀ (n₁ n₂ m : ℕ) (ι : Type) [Fintype ι] [Nonempty ι]
          (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
          0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
          0 < B → 0 ≤ sigmaSq → 0 ≤ t →
          (∀ a : ι, ∃ a' : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
            coeff a' i j = -coeff a i j) →
          (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
            |coeff a i j| ≤ B) →
          (∀ a : ι,
            ∑ i : Fin n₁, ∑ j : Fin n₂,
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  (coeff a i j) ^ 2 ≤ sigmaSq) →
          let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
          let Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
            fun Omega =>
              Finset.univ.sup' Finset.univ_nonempty
                (fun a : ι =>
                  ∑ i : Fin n₁, ∑ j : Fin n₂,
                    (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                      coeff a i j))
          bernoulliEventProb p
              (fun Omega => |Z Omega - bernoulliExpectation p Z| ≤ t) ≥
            1 -
              3 * Real.exp
                (-(t / (K * B)) *
                  Real.log
                    (1 + (B * t) /
                      (sigmaSq + B * bernoulliExpectation p Z)))) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ m : ℕ) (ι : Type) (Z : Finset (Fin n₁ × Fin n₂) → ℝ)
        (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ Omega,
          Z Omega =
            sSup {v : ℝ |
              ∃ a : ι,
                v =
                  ∑ i : Fin n₁, ∑ j : Fin n₂,
                    (((if (i, j) ∈ Omega then (1 : ℝ) else 0) -
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      coeff a i j)}) →
        (∀ a : ι, ∃ a' : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          coeff a' i j = -coeff a i j) →
        (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (coeff a i j) ^ 2 ≤ sigmaSq) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |Z Omega -
                  bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Z| ≤ t) ≥
          1 -
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq +
                      B * bernoulliExpectation
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Z))) := by sorry
