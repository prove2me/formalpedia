-- Prove2me | Theorems.Thm_ChebotarevDFT_sparse_recovery
-- name    : ChebotarevDFT.sparse_recovery
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:21:52.26783+00:00
-- url     : https://prove2.me/theorems/c2a03e7a-9076-4dd0-9f7b-8fceb4fe1fd4
-- title:
--   Sparse recovery.
-- statement:
--   **Sparse recovery.** Over `ZMod p` with `p` prime, a `k`-sparse signal is uniquely
--   determined by any `2 * k` of its Fourier coefficients.
--
--   ```lean
--   theorem ChebotarevDFT.sparse_recovery(hp : p.Prime) {k : ℕ} (Φ Ψ : ZMod p → ℂ)
--       (hΦ : (supp Φ).card ≤ k) (hΨ : (supp Ψ).card ≤ k)
--       (S : Finset (ZMod p)) (hS : 2 * k ≤ S.card) (heq : ∀ s ∈ S, 𝓕 Φ s = 𝓕 Ψ s) :
--       Φ = Ψ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ChebotarevUncertainty.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ChebotarevUncertainty.lean#L286

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








/-! ## Exact recovery of sparse signals -/

theorem ChebotarevDFT.sparse_recovery(hp : p.Prime) {k : ℕ} (Φ Ψ : ZMod p → ℂ)
    (hΦ : (supp Φ).card ≤ k) (hΨ : (supp Ψ).card ≤ k)
    (S : Finset (ZMod p)) (hS : 2 * k ≤ S.card) (heq : ∀ s ∈ S, 𝓕 Φ s = 𝓕 Ψ s) :
    Φ = Ψ := by sorry
