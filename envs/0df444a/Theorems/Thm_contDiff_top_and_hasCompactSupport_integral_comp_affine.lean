-- Prove2me | Theorems.Thm_contDiff_top_and_hasCompactSupport_integral_comp_affine
-- name    : contDiff_top_and_hasCompactSupport_integral_comp_affine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/5d252805-d07e-571f-aee0-4c5e547f5c1d
-- title:
--   Smoothness and compact support of an affine-family integral
-- statement:
--   Let $E$ and $F$ be finite-dimensional real normed spaces, and let $\Psi : F \to \mathbb{C}$ be $C^\infty$ (in the sense of `ContDiff ℝ ⊤`) with compact support. Let $P$ be a topological space carrying a measurable structure that is the Borel structure of its topology, and let $\mu$ be a finite measure on $P$. Suppose $K \subseteq P$ is compact with $\mu(K^{c}) = 0$, so that $\mu$ is carried by $K$. Let $c : P \to \mathbb{C}$ be continuous, let $A : P \to (E \to_{L[\mathbb{R}]} F)$ be a continuous family of continuous $\mathbb{R}$-linear maps, and let $b : P \to F$ be continuous. Assume there is a real constant $C$ with the uniform properness bound $\|e\| \le C\,(\|A(p)e\| + 1)$ for all $p \in K$ and all $e \in E$. Then the function
--   $$e \mapsto \int_P c(p)\,\Psi\bigl(A(p)e + b(p)\bigr)\, d\mu(p)$$
--   on $E$ is $C^\infty$ and has compact support; both assertions are delivered as a conjunction.
--
--   This is differentiation under the integral sign, in a form adapted to an affinely parametrised family of arguments of a fixed smooth compactly supported test function, with the uniform properness hypothesis supplying the compactness of the support of the resulting integral. It serves as the abstract regularity statement for archimedean factors of integrated kernels, and is used in the treatment of twisted unipotent terms, in particular by [`AutomorphicForm.TwistedBruhat.continuous_and_hasCompactSupport_and_contDiff_integral_archWord`](thm.html#AutomorphicForm.TwistedBruhat.continuous_and_hasCompactSupport_and_contDiff_integral_archWord) and [`AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_contDiff_top_and_hasCompactSupport_integral_comp_affine.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem contDiff_top_and_hasCompactSupport_integral_comp_affine
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (Ψ : F → ℂ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ)
    {P : Type*} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (K : Set P) (hK : IsCompact K) (hμK : μ Kᶜ = 0)
    (c : P → ℂ) (hc : Continuous c)
    (A : P → (E →L[ℝ] F)) (hA : Continuous A) (b : P → F) (hb : Continuous b)
    (C : ℝ) (hproper : ∀ p ∈ K, ∀ e : E, ‖e‖ ≤ C * (‖A p e‖ + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun e : E => ∫ p, c p * Ψ (A p e + b p) ∂μ) ∧
      HasCompactSupport (fun e : E => ∫ p, c p * Ψ (A p e + b p) ∂μ) := by sorry
