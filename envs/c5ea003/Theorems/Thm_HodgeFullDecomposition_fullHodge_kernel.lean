-- Prove2me | Theorems.Thm_HodgeFullDecomposition_fullHodge_kernel
-- name    : HodgeFullDecomposition.fullHodge_kernel
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:43:14.242156+00:00
-- url     : https://prove2.me/theorems/9d8278ca-128c-48a1-bafb-95a574bc182e
-- title:
--   FullHodge kernel
-- statement:
--   Formal statement of `HodgeFullDecomposition.fullHodge_kernel` from the Aether Catalog (Speculative). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem HodgeFullDecomposition.fullHodge_kernel(D : Matrix (Fin p) (Fin n) ℝ) (E : Matrix (Fin n) (Fin q) ℝ)
--       (x : Fin n → ℝ) :
--       (fullHodge D E) *ᵥ x = 0 ↔ D *ᵥ x = 0 ∧ Eᵀ *ᵥ x = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/HodgeFullDecomposition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/HodgeFullDecomposition.lean#L104

-- Thm stub generated from Speculative/AutoResearch/HodgeFullDecomposition.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_HodgeFullDecomposition
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The Full Hodge Decomposition: Down + Up Laplacian and the Harmonic Obstruction

This file *extends* the up-only skeleton of
`Catalog/Speculative/AutoResearch/HodgeSpectralThreshold.lean` (theorems
`hodge_quadform`, `hodge_psd`, `harmonic_iff_boundary`) from the single up-Laplacian
`L = Bᵀ B` to the genuine combinatorial **Hodge Laplacian** on `k`-cochains, built from
*two* boundary maps.

For boundary operators
* `∂ₖ` realized as a matrix `D : C_k → C_{k-1}`  (the *down* / divergence map), and
* `∂ₖ₊₁` realized as a matrix `E : C_{k+1} → C_k`  (the *up* / gradient map),

the Hodge Laplacian on `C_k` is

  `L = Dᵀ D + E Eᵀ`   (`fullHodge D E`),

a sum of the *down* Laplacian `Dᵀ D` and the *up* Laplacian `E Eᵀ`.  The Dirichlet
energy splits as a sum of two squared norms, and the chain condition `∂ₖ ∂ₖ₊₁ = 0`
(`D * E = 0`) makes the two energy channels orthogonal.

## Main results

* `fullHodge_isSymm`        — the full Hodge Laplacian is symmetric.
* `fullHodge_quadform`      — `⟨x, Lx⟩ = ‖Dx‖² + ‖Eᵀx‖²` (split Dirichlet energy).
* `fullHodge_psd`           — `L` is positive semidefinite.
* `fullHodge_kernel`        — **discrete Hodge theorem**: a cochain is *harmonic*
    (`Lx = 0`) iff it is simultaneously **closed** (`Dx = 0`) and **coclosed**
    (`Eᵀx = 0`); this refines `harmonic_iff_boundary` to the genuine cohomological
    invariant `ker ∂ₖ ∩ ker ∂ₖ₊₁ᵀ`.
* `hodge_image_orthogonal`  — under `∂ₖ ∂ₖ₊₁ = 0`, the gradient image `im E` is
    orthogonal to the divergence image `im Dᵀ`.
* `hodge_energy_pythagoras` — Pythagoras for the Hodge splitting: the energy of a
    gradient-plus-curl field is the sum of the two energies.

## Catalog synthesis

This realizes **Research Direction 2** of `HodgeSpectralThreshold`'s FUTURE_DIRECTIONS:
the cross term `⟨Dx, Eᵀx⟩`-type interference vanishes exactly when `∂∂ = 0`, turning the
two Dirichlet energies into an orthogonal sum so harmonicity decouples into "closed" and
"coclosed".  It bridges the *MachineLearning* domain (higher-order/simplicial message
passing) with algebraic topology (the discrete Hodge theorem and Betti numbers).
-/

open HodgeFullDecomposition

open Matrix

variable {p n q : ℕ}

-- !-- Lab Notebook -- !--
-- Hypothesis: The single up-Laplacian identity `⟨x, BᵀB x⟩ = ‖Bx‖²` should generalize to
--   the two-map Hodge Laplacian `Dᵀ D + E Eᵀ`, splitting the energy into a "closed" and a
--   "coclosed" channel, with the chain condition `∂∂ = 0` making the channels orthogonal.
--   genuine discrete Hodge theorem (harmonic = closed ∧ coclosed), and the orthogonality
--   `hodge_image_orthogonal` is the *only* place where `D * E = 0` is consumed.
-- Insight: The whole decomposition rests on bilinearity of `dotProduct` plus the two
--   transpose-adjunction lemmas `vecMul_transpose` / `mulVec_transpose`; the harmonic
--   characterization is then pure nonnegativity (`Finset.sum_nonneg` + `mul_self_nonneg`)
--   followed by `dotProduct_self_eq_zero`.  No spectral theorem is needed.
-- Failure analysis: `positivity` cannot see the `dotProduct` sum-of-products as a sum of
--   squares (entries are `v i * v i`, not `(v i)^2`), so each nonnegativity fact is built
--   by hand.  The `D * E = 0` hypothesis is genuinely unnecessary for the kernel split —
--   that fact uses only PSD of each summand — and is reserved for the orthogonality lemmas.
-- !-- end Lab Notebook -- !--


-- !-- `(Dᵀ D + E Eᵀ)ᵀ = Dᵀ D + E Eᵀ` since each summand is a symmetric Gram matrix. -- !--

-- !-- Split Dirichlet energy: distribute `dotProduct` over the sum, then apply the
--    up-Laplacian identity to each Gram summand via `mulVec_mulVec` and the two
--    transpose-adjunctions `vecMul_transpose` / `mulVec_transpose`. -- !--

-- !-- The Dirichlet energy is a sum of two sums of squares, hence nonnegative. -- !--

-- !-- Discrete Hodge theorem.  `(→)`: `Lx = 0` forces the *sum* of two nonnegative
--    energies to vanish, so each vanishes, and `dotProduct_self_eq_zero` gives `Dx = 0`,
--    `Eᵀx = 0`.  `(←)`: both vanish, so `Lx = Dᵀ(Dx) + E(Eᵀx) = 0`. -- !--

theorem HodgeFullDecomposition.fullHodge_kernel(D : Matrix (Fin p) (Fin n) ℝ) (E : Matrix (Fin n) (Fin q) ℝ)
    (x : Fin n → ℝ) :
    (fullHodge D E) *ᵥ x = 0 ↔ D *ᵥ x = 0 ∧ Eᵀ *ᵥ x = 0 := by sorry
