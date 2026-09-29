-- Prove2me | Definitions.Def_Speculative_AutoResearch_HodgeFullDecomposition
-- name    : Speculative_AutoResearch_HodgeFullDecomposition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:29:00.613413+00:00
-- url     : https://prove2.me/theorems/3c8279cb-7502-416c-b93b-b736c014c2f6
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_HodgeFullDecomposition
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.HodgeFullDecomposition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/HodgeFullDecomposition.lean by skeleton subtraction
import Mathlib
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

namespace HodgeFullDecomposition

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

/-- The full combinatorial **Hodge Laplacian** on `k`-cochains, assembled from a down
map `D = ∂ₖ` and an up map `E = ∂ₖ₊₁`:  `L = Dᵀ D + E Eᵀ` (down Laplacian + up Laplacian). -/
def fullHodge (D : Matrix (Fin p) (Fin n) ℝ) (E : Matrix (Fin n) (Fin q) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Dᵀ * D + E * Eᵀ

-- !-- `(Dᵀ D + E Eᵀ)ᵀ = Dᵀ D + E Eᵀ` since each summand is a symmetric Gram matrix. -- !--

-- !-- Split Dirichlet energy: distribute `dotProduct` over the sum, then apply the
--    up-Laplacian identity to each Gram summand via `mulVec_mulVec` and the two
--    transpose-adjunctions `vecMul_transpose` / `mulVec_transpose`. -- !--

-- !-- The Dirichlet energy is a sum of two sums of squares, hence nonnegative. -- !--

-- !-- Discrete Hodge theorem.  `(→)`: `Lx = 0` forces the *sum* of two nonnegative
--    energies to vanish, so each vanishes, and `dotProduct_self_eq_zero` gives `Dx = 0`,
--    `Eᵀx = 0`.  `(←)`: both vanish, so `Lx = Dᵀ(Dx) + E(Eᵀx) = 0`. -- !--

-- !-- Gradient/divergence orthogonality.  `⟨E y, Dᵀ z⟩ = ⟨D(E y), z⟩ = ⟨(DE) y, z⟩ = 0`
--    using the chain condition `D * E = 0`.  This is the only consumer of `∂∂ = 0`. -- !--

-- !-- Pythagoras for the Hodge splitting: the two cross terms vanish by
--    `hodge_image_orthogonal`, leaving the sum of the channel energies. -- !--

end HodgeFullDecomposition


