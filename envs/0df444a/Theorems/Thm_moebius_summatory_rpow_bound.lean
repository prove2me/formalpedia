-- Prove2me | Theorems.Thm_moebius_summatory_rpow_bound
-- name    : moebius_summatory_rpow_bound
-- status  : Open
-- author  : @ryanshin
-- created : 2026-09-05T02:34:49.008214+00:00
-- url     : https://prove2.me/theorems/96ba5204-297e-4607-9280-5e934a948a0d
-- title:
--   Open RH criterion: Mertens square-root bounds with arbitrary positive epsilon
-- statement:
--   Let $\mu$ denote the arithmetic Moebius function, and let
--
--   $$M(N)=\sum_{n=1}^{N}\mu(n)\qquad(N\in\mathbb N).$$
--
--   The assertion is that, for every real $\varepsilon>0$,
--
--   $$M(N)=O_\varepsilon\!\left(N^{1/2+\varepsilon}\right)\qquad(N\to\infty).$$
--
--   Equivalently, for every positive $\varepsilon$ there is a constant $C_\varepsilon>0$, independent of $N$, such that
--
--   $$|M(N)|\le C_\varepsilon N^{1/2+\varepsilon}\qquad(N\ge1).$$
--
--   This is an OPEN conjectural assertion equivalent to the Riemann Hypothesis, as stated in Titchmarsh and Heath-Brown, Theorem 14.25(C). It is not the disproved Mertens conjecture with constant one and exponent exactly one half. The constant here may depend on epsilon, and epsilon must be strictly positive. The assertion isolates the arithmetic cancellation needed for holomorphic continuation of the Moebius Dirichlet series into the half-plane of real part greater than one half.
--
--   **Formalization Note.** The signed integer sum is embedded into the complex numbers. Its complex norm equals its ordinary absolute value; the Lean IsBigO predicate expresses the asymptotic estimate above.
-- source:
--   E. C. Titchmarsh, The Theory of the Riemann Zeta-function, 2nd ed., revised by D. R. Heath-Brown, Oxford University Press, 1986, Section 14.25, Theorem 14.25(C), equation (14.25.2), p. 370, and its concluding converse paragraph. https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf . The cited theorem establishes equivalence with RH; the growth assertion itself remains open.

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff

theorem moebius_summatory_rpow_bound :
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) := by sorry
