-- Prove2me | Theorems.Thm_ChebotarevDFT_extremal_kernel_unique
-- name    : ChebotarevDFT.extremal_kernel_unique
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:21:43.813018+00:00
-- url     : https://prove2.me/theorems/505e957f-1d1e-4fbc-9c16-1ed3a26b57eb
-- title:
--   Rigidity of the extremal kernel.
-- statement:
--   **Rigidity of the extremal kernel.** If `#A = #S + 1`, then the space of functions
--   supported in `A` whose Fourier transform vanishes on `S` is at most one-dimensional: any two
--   such functions are proportional. Together with `exists_supported_vanishing` this pins the
--   space down to exactly a line.
--
--   ```lean
--   theorem ChebotarevDFT.extremal_kernel_unique(hp : p.Prime) (A S : Finset (ZMod p))
--       (hcard : A.card = S.card + 1) (f g : ZMod p → ℂ)
--       (hf : ∀ x ∉ A, f x = 0) (hg : ∀ x ∉ A, g x = 0)
--       (hfv : ∀ s ∈ S, 𝓕 f s = 0) (hgv : ∀ s ∈ S, 𝓕 g s = 0) (hf0 : f ≠ 0) :
--       ∃ c : ℂ, g = c • f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ChebotarevUncertainty.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ChebotarevUncertainty.lean#L230

-- Thm stub generated from Novelty/ChebotarevUncertainty.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevDFT
import Definitions.Def_Novelty_ChebotarevUncertainty
/-
# Consequences of Chebotarev's theorem: the prime-order uncertainty principle

Building on `ChebotarevDFT.det_ne_zero` (every square submatrix of the `p × p` DFT matrix is
nonsingular for `p` prime) we derive:

* `ChebotarevDFT.uncertainty` : Tao's uncertainty principle, `#supp Φ + #supp (𝓕 Φ) ≥ p + 1`
  for every nonzero `Φ : ZMod p → ℂ`;
* `ChebotarevDFT.uncertainty_sharp_delta` : the bound is attained by a Dirac mass;
* `ChebotarevDFT.sparse_recovery` : a `k`-sparse signal on `ZMod p` is determined by *any*
  `2 * k` of its Fourier coefficients (exact recovery in compressed sensing);
* `ChebotarevDFT.singular_submatrix_of_composite` : for the composite modulus `4` the analogous
  statement fails, so primality is essential.
-/

open ChebotarevDFT

open Finset Matrix Complex ZMod
open scoped ZMod

variable {p : ℕ} [NeZero p]



/-! ## The standard additive character as a power of a primitive root -/



/-! ## The uncertainty principle -/


/-! ## Sharpness -/

theorem ChebotarevDFT.extremal_kernel_unique(hp : p.Prime) (A S : Finset (ZMod p))
    (hcard : A.card = S.card + 1) (f g : ZMod p → ℂ)
    (hf : ∀ x ∉ A, f x = 0) (hg : ∀ x ∉ A, g x = 0)
    (hfv : ∀ s ∈ S, 𝓕 f s = 0) (hgv : ∀ s ∈ S, 𝓕 g s = 0) (hf0 : f ≠ 0) :
    ∃ c : ℂ, g = c • f := by sorry
