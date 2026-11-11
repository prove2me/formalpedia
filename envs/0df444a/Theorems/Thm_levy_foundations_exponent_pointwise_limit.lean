-- Prove2me | Theorems.Thm_levy_foundations_exponent_pointwise_limit
-- name    : levy_foundations_exponent_pointwise_limit
-- status  : Proved
-- author  : @Secousses
-- created : 2026-11-10T08:37:54.373906+00:00
-- url     : https://prove2.me/theorems/ca061650-ce06-4e36-8f24-5d5f99f9e5a4
-- title:
--   Continuous pointwise limits of Lévy–Khintchine exponents are Lévy–Khintchine exponents
-- statement:
--   Let $(T_n)_{n\ge1}$ be Lévy–Khintchine triples $(b_n,\sigma_n^2,\nu_n)$ with exponents
--   $$\psi_n(\xi)=ib_n\xi-\tfrac12\sigma_n^2\xi^2+\int_{\mathbb R}\bigl(e^{i\xi x}-1-i\xi x\,\mathbf 1_{\{|x|<1\}}\bigr)\,\nu_n(dx),$$
--   where each $\nu_n$ is a Lévy measure ($\nu_n\{0\}=0$ and $\int\min(1,x^2)\,d\nu_n<\infty$). Suppose that $\psi_n(\xi)\to\psi(\xi)$ for every real $\xi$ and that the limit $\psi:\mathbb R\to\mathbb C$ is continuous. Then $\psi$ is itself a Lévy–Khintchine exponent: there is a triple $U=(b,\sigma^2,\nu)$ with $\psi=\psi_U$.
--
--   This is the compactness step of the Lévy–Khintchine theorem: a pointwise limit of exponents that is continuous at $0$ stays in the class. A proof goes through the finite measures $\Lambda_n=\tfrac{\sigma_n^2}{6}\delta_0+(1-\tfrac{\sin x}{x})\,\nu_n(dx)$ obtained by averaging $-\operatorname{Re}\psi_n$ over $\xi\in[0,1]$: their masses are bounded, and tightness follows from the continuity of $\psi$ at $0$; a weakly convergent subsequence is extracted, the Lévy measure and the Gaussian part are read off from the limit, and the drift is recovered from $\operatorname{Im}\psi_n(1)$ after moving the truncation radius to a point carrying no mass.
--
--   *Formalization note.* This is a derived subproblem of `levy_foundations_semigroup_exponent_is_levyKhintchine`: for a convolution semigroup with exponent $\psi$ the compound Poisson approximants $n(e^{\psi/n}-1)$ are exponents of triples converging pointwise to $\psi$, so this statement closes that leaf.
-- source:
--   Derived subproblem. Compare K. Sato, Lévy Processes and Infinitely Divisible Distributions (1999), Theorem 8.7 and Theorem 8.1; O. Kallenberg, Foundations of Modern Probability (2nd ed., 2002), Theorem 15.14.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent

open MeasureTheory ProbabilityTheory

theorem levy_foundations_exponent_pointwise_limit
    (T : ℕ → LevyFoundations.LevyKhintchineTriple) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hlim : ∀ ξ : ℝ, Filter.Tendsto (fun n => LevyFoundations.exponent (T n) ξ) Filter.atTop (nhds (ψ ξ))) :
    ∃ U : LevyFoundations.LevyKhintchineTriple, ∀ ξ : ℝ, ψ ξ = LevyFoundations.exponent U ξ := by sorry
