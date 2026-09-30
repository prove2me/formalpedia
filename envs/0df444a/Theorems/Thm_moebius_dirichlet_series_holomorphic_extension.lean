-- Prove2me | Theorems.Thm_moebius_dirichlet_series_holomorphic_extension
-- name    : moebius_dirichlet_series_holomorphic_extension
-- status  : Open
-- author  : @ryanshin
-- created : 2026-09-05T02:20:46.528029+00:00
-- url     : https://prove2.me/theorems/3f160e74-767e-439f-a8d7-86209c799b83
-- title:
--   Open RH criterion: holomorphic continuation of the Moebius Dirichlet series
-- statement:
--   Let $\mu$ be the arithmetic Moebius function. The assertion is that there exists a complex-valued function $F$ holomorphic on the half-plane
--
--   $$H=\{s\in\mathbb C:\operatorname{Re}s>\tfrac12\}$$
--
--   whose restriction to the half-plane of absolute convergence satisfies
--
--   $$F(s)=\sum_{n=1}^{\infty}\frac{\mu(n)}{n^s}\qquad(\operatorname{Re}s>1).$$
--
--   This is an OPEN conjectural criterion, retaining the unresolved difficulty of the Riemann Hypothesis. It is the analytic-continuation intermediate assertion in the classical Moebius-series criterion; it is not an unconditional consequence of the cited theorem. Titchmarsh's Theorem 14.25(A) proves the stronger ordered-series convergence statement under RH, while the analytic-continuation argument preceding Theorem 14.25(B) supplies the converse implication to RH.
--
--   **Formalization Note.** The conclusion requires existence of a holomorphic extension. It uses Lean's LSeries only where the real part exceeds one and makes no claim of absolute summability for real part between one half and one.
-- source:
--   E. C. Titchmarsh, The Theory of the Riemann Zeta-function, 2nd ed., revised by D. R. Heath-Brown, Oxford University Press, 1986, Section 14.25, Theorem 14.25(A), p. 369, and the analytic-continuation paragraph preceding Theorem 14.25(B), p. 370. https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf . This open assertion formalizes the holomorphic-continuation intermediate criterion, not the full ordered-series convergence statement.

import Mathlib.NumberTheory.LSeries.Dirichlet

theorem moebius_dirichlet_series_holomorphic_extension :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        F s = LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s := by sorry
