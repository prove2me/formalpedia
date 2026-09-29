-- Prove2me | Theorems.Thm_ChebotarevDFT_mem_supp
-- name    : ChebotarevDFT.mem_supp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:21:26.217562+00:00
-- url     : https://prove2.me/theorems/6da05e3b-a30c-4405-9154-4047211b0e45
-- title:
--   Mem supp
-- statement:
--   Formal statement of `ChebotarevDFT.mem_supp` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ChebotarevDFT.mem_supp{Φ : ZMod p → ℂ} {x : ZMod p} : x ∈ supp Φ ↔ Φ x ≠ 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ChebotarevUncertainty.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ChebotarevUncertainty.lean#L28

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

theorem ChebotarevDFT.mem_supp{Φ : ZMod p → ℂ} {x : ZMod p} : x ∈ supp Φ ↔ Φ x ≠ 0 := by sorry
