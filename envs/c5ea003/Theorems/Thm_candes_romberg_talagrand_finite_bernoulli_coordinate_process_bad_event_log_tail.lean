-- Prove2me | Theorems.Thm_candes_romberg_talagrand_finite_bernoulli_coordinate_process_bad_event_log_tail
-- name    : candes_romberg_talagrand_finite_bernoulli_coordinate_process_bad_event_log_tail
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-29T22:51:33.883811+00:00
-- url     : https://prove2.me/theorems/c21db2ac-0b75-43c0-a2d4-e8fe1750653d
-- statement:
--   This is the bad-event form of the finite Bernoulli-coordinate Talagrand concentration input used in the Candes--Romberg theorem and cited by Candes--Recht Appendix 9.1.
--
--   Source: Candes--Romberg, *Sparsity and incoherence in compressive sampling*, PDF p. 11, Theorem 3.2, equation (3.9). Candes--Recht, *Exact Matrix Completion via Convex Optimization*, Appendix 9.1, PDF p. 46, Theorem 9.1 and equations (9.1)--(9.2), cites the same Talagrand--Ledoux empirical-process concentration input.
--
--   Mathematical statement and notation: let $p=m/(n_1n_2)$ and let $\Omega\subseteq [n_1]\times[n_2]$ be sampled in the independent Bernoulli model. For a finite nonempty coefficient class $c_a(i,j)$ indexed by $a\in\iota$, define
--   $$
--   S_a(\Omega)=\sum_{i,j}(1_{(i,j)\in\Omega}-p)c_a(i,j),\qquad
--   Z(\Omega)=\max_a S_a(\Omega),\qquad
--   \bar Z(\Omega)=\max_a |S_a(\Omega)|.
--   $$
--   Assume the envelope bound $|c_a(i,j)|\le B$ and the variance proxy bound
--   $$
--   \sum_{i,j}p(1-p)c_a(i,j)^2\le \sigma^2
--   $$
--   for every $a$. Then there is a universal $K>0$ such that for every $t\ge0$,
--   $$
--   \mathbb P_p\{|Z-\mathbb E_p Z|>t\}
--   \le
--   3\exp\left(-{t\over KB}\log\left(1+{Bt\over \sigma^2+B\mathbb E_p\bar Z}\right)\right).
--   $$
--   Here $n_1,n_2,m,p,B,\sigma^2,t,Z,\bar Z$ are exactly the quantities used in the target theorem `candes_romberg_talagrand_finite_bernoulli_coordinate_process_log_tail`; the coherence parameters $\mu_0,\mu_1$ and `successProb` do not appear in this external concentration leaf.
--
--   Formalization note: this is a direct source theorem / source-derived formulation, not a Lean-only arithmetic bridge. It records the source theorem in the usual bad-event probability form. The parent `candes_romberg_talagrand_finite_bernoulli_coordinate_process_log_tail` is the equivalent good-event lower-bound form and should be connected by the formal complement identity for `bernoulliEventProb`.
-- source:
--   Candes--Romberg, *Sparsity and incoherence in compressive sampling*, PDF p. 11, Theorem 3.2, equation (3.9); cited by Candes--Recht, *Exact Matrix Completion via Convex Optimization*, Appendix 9.1, PDF p. 46, Theorem 9.1 and equations (9.1)--(9.2).

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MatrixCompletion
open scoped Classical BigOperators

theorem candes_romberg_talagrand_finite_bernoulli_coordinate_process_bad_event_log_tail :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ m : ℕ) (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (coeff a i j) ^ 2 ≤ sigmaSq) →
        let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
        let process : ι → Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun a Omega =>
            ∑ i : Fin n₁, ∑ j : Fin n₂,
              (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                coeff a i j)
        let Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun Omega =>
            Finset.univ.sup' Finset.univ_nonempty (fun a : ι => process a Omega)
        let Zbar : Finset (Fin n₁ × Fin n₂) → ℝ :=
          fun Omega =>
            Finset.univ.sup' Finset.univ_nonempty
              (fun a : ι => |process a Omega|)
        bernoulliEventProb p
            (fun Omega => ¬ |Z Omega - bernoulliExpectation p Z| ≤ t) ≤
          3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq + B * bernoulliExpectation p Zbar))) := by
  sorry
