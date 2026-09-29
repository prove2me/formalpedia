-- Prove2me | Theorems.Thm_RandomMatrices_airyKernel_diagonal_tendsto
-- name    : RandomMatrices.airyKernel_diagonal_tendsto
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:27:39.353987+00:00
-- url     : https://prove2.me/theorems/39b8fa0a-003a-45b7-8317-4274cb1684ed
-- title:
--   Diagonal value of the Airy kernel is the (constant) Wronskian.
-- statement:
--   **Diagonal value of the Airy kernel is the (constant) Wronskian.**
--
--   As `y → x`, the off-diagonal kernel `K(x,y)` converges to `−W`, where
--   `W = airyWronskian f f' g g'`.  For solutions of the Airy equation `W` is
--   *constant* (`airyWronskian_const`), so the limiting diagonal value `−W(0)` is the
--   *same* at every base point `x` — the removable singularity is uniform along the
--   diagonal.
--
--   ```lean
--   theorem RandomMatrices.airyKernel_diagonal_tendsto    (f f' f'' g g' g'' : ℝ → ℝ)
--       (hf : ∀ x, HasDerivAt f (f' x) x)
--       (hf' : ∀ x, HasDerivAt f' (f'' x) x)
--       (hg : ∀ x, HasDerivAt g (g' x) x)
--       (hg' : ∀ x, HasDerivAt g' (g'' x) x)
--       (eqf : ∀ x, f'' x = x * f x)
--       (eqg : ∀ x, g'' x = x * g x)
--       (x : ℝ) :
--       Filter.Tendsto (fun y => airyKernel f g x y) (𝓝[≠] x)
--         (𝓝 (-(airyWronskian f f' g g' 0))) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AiryKernel.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AiryKernel.lean#L45

-- Thm stub generated from Novelty/AiryKernel.lean
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

theorem RandomMatrices.airyKernel_diagonal_tendsto    (f f' f'' g g' g'' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (eqf : ∀ x, f'' x = x * f x)
    (eqg : ∀ x, g'' x = x * g x)
    (x : ℝ) :
    Filter.Tendsto (fun y => airyKernel f g x y) (𝓝[≠] x)
      (𝓝 (-(airyWronskian f f' g g' 0))) := by sorry
