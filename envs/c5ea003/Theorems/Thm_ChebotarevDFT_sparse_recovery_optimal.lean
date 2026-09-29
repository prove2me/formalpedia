-- Prove2me | Theorems.Thm_ChebotarevDFT_sparse_recovery_optimal
-- name    : ChebotarevDFT.sparse_recovery_optimal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:21:50.907108+00:00
-- url     : https://prove2.me/theorems/3d042fa9-e4d2-4bfb-8ad6-97d7912d6ab7
-- title:
--   **Optimality of the `2 * k` sample bound.** With only `2 * k - 1` prescribed frequencies
-- statement:
--   **Optimality of the `2 * k` sample bound.** With only `2 * k - 1` prescribed frequencies
--   there are always two distinct `k`-sparse signals with the same Fourier coefficients on that
--   set, so `sparse_recovery` cannot be improved.
--
--   ```lean
--   theorem ChebotarevDFT.sparse_recovery_optimal(k : ℕ) (hk1 : 1 ≤ k) (hk : 2 * k ≤ p)
--       (S : Finset (ZMod p)) (hS : S.card = 2 * k - 1) :
--       ∃ f g : ZMod p → ℂ, f ≠ g ∧ (supp f).card ≤ k ∧ (supp g).card ≤ k ∧
--         ∀ s ∈ S, 𝓕 f s = 𝓕 g s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ChebotarevUncertainty.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ChebotarevUncertainty.lean#L321

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

theorem ChebotarevDFT.sparse_recovery_optimal(k : ℕ) (hk1 : 1 ≤ k) (hk : 2 * k ≤ p)
    (S : Finset (ZMod p)) (hS : S.card = 2 * k - 1) :
    ∃ f g : ZMod p → ℂ, f ≠ g ∧ (supp f).card ≤ k ∧ (supp g).card ≤ k ∧
      ∀ s ∈ S, 𝓕 f s = 𝓕 g s := by sorry
