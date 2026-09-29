-- Prove2me | Theorems.Thm_moebius_summatory_rpow_bound
-- name    : moebius_summatory_rpow_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-10T19:17:20.327316+00:00
-- url     : https://prove2.me/theorems/292f61ee-b8e1-40cd-a590-4c1ab11c7500
-- title:
--   Open RH criterion: Mertens square-root bounds with arbitrary positive epsilon
-- statement:
--   Let $\mu$ denote the arithmetic Moebius function, and let
--
--   $$M(N)=\sum_{n=1}^{N}\mu(n)\qquad(N\in\mathbb N).$$
--
--   The assertion is that, for every real $\varepsilon>0$,
--
--   $$M(N)=O_\varepsilon\!\left(N^{1/2+\varepsilon}\right)\qquad(N\to\infty),$$
--
--   that is, for every positive $\varepsilon$ there is a constant $C_\varepsilon>0$, independent of $N$, with
--
--   $$|M(N)|\le C_\varepsilon N^{1/2+\varepsilon}\qquad(N\ge1).$$
--
--   This is an open conjectural assertion, equivalent to the Riemann Hypothesis, as stated in Titchmarsh and Heath-Brown, Theorem 14.25(C). It is not the disproved Mertens conjecture, which asks for the constant one and the exponent exactly one half: here the constant is allowed to depend on $\varepsilon$, and $\varepsilon$ is strictly positive. The assertion isolates the arithmetic cancellation needed for the holomorphic continuation of the Moebius Dirichlet series $\sum_{n\ge1}\mu(n)n^{-s}$ into the half-plane $\operatorname{Re} s>\tfrac12$.
--
--   **Formalization Note.** The signed integer partial sum is embedded into the complex numbers; its complex norm is its ordinary absolute value, and the Lean `IsBigO` predicate along `atTop` expresses the asymptotic estimate above. This is the statement `moebius_summatory_rpow_bound`, recreated verbatim in the Mathlib `777aaa6` environment so that theorems of that environment can cite it.
-- source:
--   E. C. Titchmarsh, The Theory of the Riemann Zeta-function, 2nd ed., revised by D. R. Heath-Brown, Oxford University Press, 1986, Section 14.25, Theorem 14.25(C), equation (14.25.2), p. 370, and its concluding converse paragraph. https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf . The cited theorem establishes equivalence with RH; the growth assertion itself remains open.

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff

theorem moebius_summatory_rpow_bound :
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) := by sorry
