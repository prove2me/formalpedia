-- Prove2me | Theorems.Thm_bernoulli_rademacher_symmetrization_contraction_moment_bound
-- name    : bernoulli_rademacher_symmetrization_contraction_moment_bound
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-24T05:56:45.124145+00:00
-- url     : https://prove2.me/theorems/7ade53da-10e6-4d8a-9a01-41802dfb61bc
-- statement:
--   **Discrete Bernoulli to Rademacher symmetrization / contraction inequality (Ledoux-Talagrand, Probability in Banach Spaces (1991), Lemma 6.3; van der Vaart-Wellner, Weak Convergence and Empirical Processes (1996), Lemma 2.3.1; Tropp, arXiv:1506.04711, Fact 3.1).** A Bernoulli(p) configuration over a finite index set is encoded by a finset `S : Finset κ` (membership = the coordinate's indicator is 1), carrying the product weight `wt p S = p^|S| (1-p)^(N-|S|)` where `N = Fintype.card κ`. A Rademacher sign pattern is encoded by `Es : Finset κ` (membership = sign +1, else -1), carrying the uniform weight `rwt = 2^{-N}`. For vectors `v : κ → E` in a real normed space and any integer `q`, the q-th moment of the centered Bernoulli sum `∑_a (δ_a - p) v_a` is bounded, up to the factor `2^q`, by the doubly-averaged q-th moment of the sign-randomized sampled sum `∑_a ε_a δ_a v_a`: `E_δ ‖∑_a (δ_a - p) v_a‖^q ≤ 2^q · E_δ E_ε ‖∑_a ε_a δ_a v_a‖^q`. This is the symmetrization step (Step 1) of Rudelson's 1999 selection argument (Rudelson, JFA 164 (1999) 60-72) transcribed to the discrete product-Bernoulli model used in Section 6.1 of Candes-Recht (arXiv:0805.4471). Proof: (A) ghost copy + Jensen on the convex map `x ↦ ‖x‖^q` (constant 1); (B) for every fixed sign pattern the swap-on-complement involution of the product cube is weight-preserving and turns the ghost difference into the sign-randomized difference, so averaging over signs is free (equality); (C) triangle inequality + the tight Loève c_r bound `(a+b)^q ≤ 2^{q-1}(a^q+b^q)` followed by the S↔S' fold gives `2^{q-1}·2 = 2^q`. The convexity step uses `q ≥ 1`; `q = 0` is the trivial `1 ≤ 1`.
-- source:
--   Ledoux-Talagrand, Probability in Banach Spaces (1991), Lemma 6.3; van der Vaart-Wellner, Weak Convergence and Empirical Processes (1996), Lemma 2.3.1; Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1506.04711, Fact 3.1; Rudelson, JFA 164 (1999) 60-72; Candes-Recht, arXiv:0805.4471, Section 6.1.

import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.SymmDiff
open scoped BigOperators

theorem bernoulli_rademacher_symmetrization_contraction_moment_bound
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : κ → E) :
    (∑ S : Finset κ,
        (p ^ S.card * (1 - p) ^ (Fintype.card κ - S.card))
          * ‖∑ a, ((if a ∈ S then (1:ℝ) else 0) - p) • v a‖ ^ q)
      ≤ 2 ^ q * ∑ S : Finset κ, ∑ Es : Finset κ,
          (p ^ S.card * (1 - p) ^ (Fintype.card κ - S.card))
            * (((1:ℝ)/2) ^ Fintype.card κ)
            * ‖∑ a, ((if a ∈ Es then (1:ℝ) else -1) * (if a ∈ S then (1:ℝ) else 0)) • v a‖ ^ q := by sorry
