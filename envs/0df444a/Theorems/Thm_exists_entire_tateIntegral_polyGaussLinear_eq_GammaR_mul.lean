-- Prove2me | Theorems.Thm_exists_entire_tateIntegral_polyGaussLinear_eq_GammaR_mul
-- name    : exists_entire_tateIntegral_polyGaussLinear_eq_GammaR_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/3a035426-3448-563c-bf41-86f9df17a3d0
-- title:
--   Real Tate integrals of Gaussian times polynomial: Γ_ℝ-factorisation
-- statement:
--   Fix a natural number $n$ (a degree bound) and $\delta \in \mathbb{N}$ with $\delta \le 1$. The assertion is the existence of a single function $E$ of four arguments, a coefficient vector $c \in \mathbb{C}^{n+1}$, two reals $A, B$ and a complex $z$, with the following four properties. First, for every $c$ and all real $A, B$ (no positivity required), $z \mapsto E(c,A,B,z)$ is differentiable on all of $\mathbb{C}$, i.e. entire. Second, for every $c$, all real $A, B$ with $A > 0$, and every $z$ with $\operatorname{Re} z > 0$, the integral over $\rho \in \mathbb{R}$ of $\bigl(\sum_{j=0}^{n} c_j \rho^{j}\bigr) e^{-\pi (A\rho^{2} + 2B\rho)} \operatorname{sign}(\rho)^{\delta} |\rho|^{z-1}$ (the powers of $|\rho|$ being complex powers) equals $\Gamma_{\mathbb R}(z+\delta)\, E(c,A,B,z)$, where $\Gamma_{\mathbb R}(w) = \pi^{-w/2}\Gamma(w/2)$. Third, for every vertical strip, given by reals $\sigma_1, \sigma_2$, there are constants $C, M \in \mathbb{R}$ and $N \in \mathbb{N}$, depending only on the strip (and on $n$, $\delta$), such that for all $c$, all $A > 0$, all real $B$ and all $z$ with $\sigma_1 \le \operatorname{Re} z \le \sigma_2$, $$\|E(c,A,B,z)\| \le C \Bigl(\sum_{j} \|c_j\|\Bigr) \max(A, A^{-1})^{N} (1+|B|)^{N} e^{\pi B^{2}/A} e^{M |\operatorname{Im} z|}.$$ Fourth, for each fixed $z$, the map $(c,A,B) \mapsto E(c,A,B,z)$ is continuous on the set where $A > 0$.
--
--   This is the archimedean (real-place) local computation behind Tate-style integrals: the Mellin transform of a polynomial times a Gaussian with a linear term factors as the real Gamma factor $\Gamma_{\mathbb R}(z+\delta)$ times an entire function whose growth in vertical strips and dependence on the Gaussian data are controlled uniformly. It is used in the cubic-induction step of the Langlands–Tunnell argument, where the analogous unfolding integral is shown to be $\Gamma_{\mathbb R}$ times a differentiable function; the estimate rests on the two-sided bounds for $\|\Gamma\|$ in vertical strips.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_entire_tateIntegral_polyGaussLinear_eq_GammaR_mul.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Data.Real.Sign

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem exists_entire_tateIntegral_polyGaussLinear_eq_GammaR_mul (n δ : ℕ) (hδ : δ ≤ 1) :
    ∃ E : (Fin (n + 1) → ℂ) → ℝ → ℝ → ℂ → ℂ,
      (∀ (c : Fin (n + 1) → ℂ) (A B : ℝ), Differentiable ℂ (E c A B)) ∧
      (∀ (c : Fin (n + 1) → ℂ) (A B : ℝ), 0 < A → ∀ z : ℂ, 0 < z.re →
        ∫ ρ : ℝ, (∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)) *
            (Real.exp (-(Real.pi * (A * ρ ^ 2 + 2 * B * ρ))) : ℂ) * (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1) =
          Complex.Gammaℝ (z + δ) * E c A B z) ∧
      (∀ σ₁ σ₂ : ℝ, ∃ (C M : ℝ) (N : ℕ), ∀ (c : Fin (n + 1) → ℂ) (A B : ℝ), 0 < A → ∀ z : ℂ, σ₁ ≤ z.re → z.re ≤ σ₂ →
        ‖E c A B z‖ ≤ C * (∑ j : Fin (n + 1), ‖c j‖) * max A A⁻¹ ^ N * (1 + |B|) ^ N *
          Real.exp (Real.pi * B ^ 2 / A) * Real.exp (M * |z.im|)) ∧
      (∀ z : ℂ, ContinuousOn (fun p : (Fin (n + 1) → ℂ) × ℝ × ℝ => E p.1 p.2.1 p.2.2 z)
        {p : (Fin (n + 1) → ℂ) × ℝ × ℝ | 0 < p.2.1}) := by sorry
