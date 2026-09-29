-- Prove2me | Theorems.Thm_ZSpan_norm_setIntegral_fundamentalDomain_cexp_mul_le_inv_pow_mul_setIntegral_norm_of_hasDerivAt
-- name    : ZSpan.norm_setIntegral_fundamentalDomain_cexp_mul_le_inv_pow_mul_setIntegral_norm_of_hasDerivAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/227b93c4-f938-55a0-8c5c-fa0d84b17781
-- title:
--   Directional integration by parts on a fundamental parallelepiped
-- statement:
--   Let $E$ be a finite-dimensional real normed space, equipped with a Borel measurable structure and an additive Haar measure $\mu$, let $b$ be a basis of $E$ indexed by a finite type $\iota$, and let $\ell : E \to \mathbb{R}$ be a continuous linear form. Let $v \in E$ satisfy $\ell(v) \neq 0$, and let $H_0, H_1, H_2, \dots : E \to \mathbb{C}$ be a sequence of continuous functions such that for every $j$ and every $x \in E$ the function $t \mapsto H_j(x + t v)$ of a real variable has derivative $H_{j+1}(x)$ at $t = 0$, and such that for every $j$, every $x \in E$ and every index $i$ one has $e^{2\pi i \ell(x + b_i)} H_j(x + b_i) = e^{2\pi i \ell(x)} H_j(x)$, i.e. each product $x \mapsto e^{2\pi i \ell(x)} H_j(x)$ is invariant under translation by each basis vector. Then for every natural number $M$,
--   $$\Big\| \int_{\mathcal{F}} e^{2\pi i \ell(x)} H_0(x)\, d\mu(x) \Big\| \le (2\pi |\ell(v)|)^{-M} \int_{\mathcal{F}} \|H_M(x)\|\, d\mu(x),$$
--   where $\mathcal{F} =$ `ZSpan.fundamentalDomain b` is the fundamental parallelepiped $\{\sum_i t_i b_i : 0 \le t_i < 1\}$ of the lattice spanned by $b$, and the inverse is taken in $\mathbb{R}$ (so the factor is $1$ when $M = 0$).
--
--   This is the standard decay estimate for Fourier coefficients of smooth functions on a torus, here in a directional form: differentiation is performed only along the single vector $v$, and only the products $e^{2\pi i \ell} H_j$, not the character and the functions $H_j$ separately, are assumed periodic under the lattice. It is used to bound Whittaker coefficients of automorphic forms, via [`AutomorphicForm.exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le`](thm.html#AutomorphicForm.exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ZSpan_norm_setIntegral_fundamentalDomain_cexp_mul_le_inv_pow_mul_setIntegral_norm_of_hasDerivAt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem ZSpan.norm_setIntegral_fundamentalDomain_cexp_mul_le_inv_pow_mul_setIntegral_norm_of_hasDerivAt
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b : Module.Basis ι ℝ E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (ℓ : E →L[ℝ] ℝ) (v : E) (hv : ℓ v ≠ 0)
    (Hs : ℕ → E → ℂ) (hcont : ∀ j, Continuous (Hs j))
    (hderiv : ∀ (j : ℕ) (x : E), HasDerivAt (fun t : ℝ => Hs j (x + t • v)) (Hs (j + 1) x) 0)
    (hper : ∀ (j : ℕ) (x : E) (i : ι),
      Complex.exp (2 * Real.pi * Complex.I * ℓ (x + b i)) * Hs j (x + b i) =
        Complex.exp (2 * Real.pi * Complex.I * ℓ x) * Hs j x)
    (M : ℕ) :
    ‖∫ x in ZSpan.fundamentalDomain b, Complex.exp (2 * Real.pi * Complex.I * ℓ x) * Hs 0 x ∂μ‖ ≤
      ((2 * Real.pi * |ℓ v|)⁻¹) ^ M * ∫ x in ZSpan.fundamentalDomain b, ‖Hs M x‖ ∂μ := by sorry
