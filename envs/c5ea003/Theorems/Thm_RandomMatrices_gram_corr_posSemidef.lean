-- Prove2me | Theorems.Thm_RandomMatrices_gram_corr_posSemidef
-- name    : RandomMatrices.gram_corr_posSemidef
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:27:37.950985+00:00
-- url     : https://prove2.me/theorems/5d0c2d95-4f90-40bf-b8c3-070f7ae4eaeb
-- title:
--   `n×n` determinantal positivity.
-- statement:
--   **`n×n` determinantal positivity.**  For any finite set of base points
--   `p : Fin n → ℝ`, the correlation matrix `(K(pᵢ, pⱼ))` of a Gram correlation
--   kernel is positive semidefinite.  This is the full positivity making the Airy
--   kernel an admissible determinantal correlation kernel.
--
--   ```lean
--   theorem RandomMatrices.gram_corr_posSemidef{H : Type*} [NormedAddCommGroup H]
--       [InnerProductSpace ℝ H] {n : ℕ} (φ : ℝ → H) (p : Fin n → ℝ) :
--       (Matrix.of (fun i j => gramKernel φ (p i) (p j))).PosSemidef := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AiryKernel.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AiryKernel.lean#L114

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

theorem RandomMatrices.gram_corr_posSemidef{H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (φ : ℝ → H) (p : Fin n → ℝ) :
    (Matrix.of (fun i j => gramKernel φ (p i) (p j))).PosSemidef := by sorry
