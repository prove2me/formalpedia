-- Prove2me | solution 1 for RandomMatrices.gram_corr_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:43:04.311763+00:00
-- url     : https://prove2.me/submissions/bcb46a73-ef34-4dd1-935d-06b97b9f3108

-- Sol generated from Novelty/AiryKernel.lean
import Mathlib
import Definitions.Def_Novelty_AiryKernel
import Definitions.Def_Novelty_AiryODE
/-
# The Airy Kernel: Symmetry, Diagonal, and Determinantal Positivity

The local statistics at the spectral edge of a random matrix are a determinantal
point process with correlation kernel the **Airy kernel**.  In Christoffel–Darboux
(integrable-kernel) form it is built from two solutions `f, g` of Airy's equation:

  `K(x, y) = (f x · g y − g x · f y) / (x − y)`.

This file proves three genuine properties of this kernel and of determinantal
correlation kernels in general:

* `airyKernel_symm` — the kernel is symmetric, `K x y = K y x`.
* `airyKernel_diagonal_tendsto` — the off-diagonal kernel has a removable
  singularity on the diagonal, and its limiting diagonal value is `−W`, the
  (constant!) Wronskian.  This *reuses* `airyWronskian_const` from `AiryODE.lean`:
  the diagonal value is the *same* at every point precisely because the Wronskian
  is constant — the analytic shadow of translation structure of the Airy process.
* `gram_corr_det_nonneg` / `gram_corr_posSemidef` — for any projection-type
  (Gram) correlation kernel `K(x,y) = ⟪φ x, φ y⟫`, the `2×2` correlation
  determinant is `≥ 0` and the full `n×n` correlation matrix is positive
  semidefinite.  This is exactly the positivity that makes the Airy kernel define
  an honest determinantal point process.
-/

open Filter Topology RealInnerProductSpace

open RandomMatrices








/-
-- !-- Lab Notes -- !--

Hypothesis (Hypothesizer):
  H4. The CD Airy kernel `K(x,y)=(f x g y - g x f y)/(x-y)` is symmetric.
  H5 (surprising). The diagonal value of `K` (its removable-singularity limit) is
      `-W`, and is the SAME at every base point — a uniform diagonal — because the
      Wronskian is constant.  i.e. the singular-looking kernel is "flat" on the
      diagonal at the level of the Wronskian.
  H6 (counter-intuitive). The structural positivity of the determinantal process
      (n×n correlation matrices PSD) requires NO Airy-specific input at all: it is
      pure Cauchy–Schwarz / Gram positivity for ANY projection kernel.

Experiment (Experimenter):
  * H4: `div_eq_div_iff` + `ring` on the cross-multiplied identity.
  * H5: rewrite `K` as `-slope N x` for `N y = f x g y - g x f y` (vanishing at
    `y=x`), use `hasDerivAt_iff_tendsto_slope`; then `airyWronskian_const`
    (imported from AiryODE.lean) rewrites the position-dependent limit `-(W x)` to
    the constant `-(W 0)`.  The `field_simp; ring` reconciles `slope` with `K`.
  * H6: 2×2 case is Cauchy–Schwarz (`abs_real_inner_le_norm`); n×n case unfolds
    `vᵀ M v` to `⟪Σ vᵢφᵢ, Σ vⱼφⱼ⟫ = ‖Σ vᵢφᵢ‖² ≥ 0` via `inner_sum`/`sum_inner`.

Analysis (Analyst):
  * All SURVIVED (0 sorries).  H5 is the genuine cross-file reuse: drop
    `airyWronskian_const` and the diagonal value stays `-(W x)` — still true but no
    longer manifestly uniform.  So constancy is exactly what upgrades "removable
    singularity at each point" to "uniform diagonal".
  * Failure mode: stating the diagonal limit over the full `𝓝 x` (not the punctured
    `𝓝[≠] x`) is FALSE — `K` is undefined at `y=x`.  The punctured neighborhood is
    mandatory; `hasDerivAt_iff_tendsto_slope` is exactly tailored to it.

Critique (Critic):
  * No theorem is trivial: H4 uses `div_eq_div_iff`; H5 uses `HasDerivAt`/slope
    machinery + the imported constancy lemma; H6 uses Cauchy–Schwarz and a genuine
    PosSemidef expansion. None is `rfl`/`decide`/`native_decide`.
  * Corner case checked: `gram_corr_posSemidef` covers `n = 0` (empty matrix
    vacuously PSD) and repeated points (matrix is then singular but still PSD).

Synthesis (PI):
  Symmetry + uniform diagonal + Gram positivity are exactly the three hypotheses an
  abstract "Airy-type determinantal kernel" must satisfy; we have isolated them and
  shown which depend on the ODE (the diagonal) and which are universal (positivity).
-/
open RandomMatrices in
theorem solution{H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (φ : ℝ → H) (p : Fin n → ℝ) :
    (Matrix.of (fun i j => gramKernel φ (p i) (p j))).PosSemidef := by
  constructor
  · ext i j
    simp only [Matrix.of_apply, gramKernel, Matrix.conjTranspose_apply, star_trivial]
    exact real_inner_comm (φ (p i)) (φ (p j))
  · intro x
    -- `xᴴ M x = ⟪Σ xᵢ φ(pᵢ), Σ xⱼ φ(pⱼ)⟫ = ‖Σ xᵢ φ(pᵢ)‖² ≥ 0`
    have hS : (x.sum fun i xi => x.sum fun j xj =>
          star xi * (Matrix.of (fun i j => gramKernel φ (p i) (p j))) i j * xj)
        = ⟪x.sum (fun i xi => xi • φ (p i)), x.sum (fun i xi => xi • φ (p i))⟫ := by
      rw [Finsupp.sum, Finsupp.sum, sum_inner]
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.of_apply, gramKernel, inner_smul_left, inner_smul_right,
        star_trivial, starRingEnd_apply]
      ring
    rw [hS]
    exact real_inner_self_nonneg
