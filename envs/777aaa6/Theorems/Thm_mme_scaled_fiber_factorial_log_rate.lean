-- Prove2me | Theorems.Thm_mme_scaled_fiber_factorial_log_rate
-- name    : mme_scaled_fiber_factorial_log_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T20:41:37.244893+00:00
-- url     : https://prove2.me/theorems/7056bea9-3157-4ba5-a384-8a630ffccfa9
-- title:
--   Grouped factorial quotients have the joint-minus-marginal entropy rate
-- statement:
--   Let $C$ and $G$ be finite sets, let $\gamma:C\to G$ group cells into rows, and let $a_c,M_g\in\mathbb N$ satisfy
--   $$
--   M_g=\sum_{\gamma(c)=g}a_c\qquad(g\in G).
--   $$
--   For each integer $m\geq0$, let
--   $$
--   W_m=\prod_{g\in G}
--   \frac{(M_gm)!}{\prod_{\gamma(c)=g}(a_cm)!}.
--   $$
--   Every row quotient is the exact integer multinomial coefficient. Then
--   $$
--   \lim_{m\to\infty}\frac{\log W_m}{m}
--   =\sum_{g\in G}M_g\log M_g-\sum_{c\in C}a_c\log a_c.
--   $$
--   All logarithms are natural, with $0\log0=0$. Empty rows, zero counts, zero total, and empty indexing sets are included.
--
--   This is the actual joint-type refinement rate with a fixed row marginal, the entropy difference used when counting words in a fixed-mode star. It is a rate for one specified joint table; bounding the sum over all admissible joint tables remains a separate entropy-optimization step.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 3.6 Lemma 3.4 (multinomial entropy asymptotics) and Section 3.7 (joint and marginal index-sequence distributions), https://arxiv.org/html/2210.10173v5#S3.SS6 . Exact natural-log, denominator-cleared finite-alphabet formulation; zero counts and zero total included. Proof uses the accepted explicit two-sided regional multinomial estimate mme_regional_dependent_profile_entropy_bounds (3e9ba49e-f426-4a5a-8739-07e31d73eeb0) and derives the limit rather than assuming it.

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

open BigOperators Filter
open scoped Topology Classical
set_option autoImplicit false

theorem mme_scaled_fiber_factorial_log_rate {C G : Type*} [Fintype C] [Fintype G]
    (grade : C → G) (a : C → ℕ) (M : G → ℕ)
    (hrow : ∀ g, ∑ c : {c : C // grade c = g}, a c.val = M g) :
    Tendsto (fun m : ℕ ↦
      Real.log ((∏ g, (M g * m).factorial /
        ∏ c : {c : C // grade c = g}, (a c.val * m).factorial : ℕ) : ℝ) / (m : ℝ))
      atTop (𝓝 ((∑ g, (M g : ℝ) * Real.log (M g : ℝ)) -
        ∑ c, (a c : ℝ) * Real.log (a c : ℝ))) := by sorry
