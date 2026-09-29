-- Prove2me | Definitions.Def_Combinatorics_CausalintegrationComposition_CausalIntegration_Composition
-- name    : Combinatorics_CausalintegrationComposition_CausalIntegration_Composition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:30:09.558983+00:00
-- url     : https://prove2.me/theorems/7467a46d-b591-474f-a457-68ffe7ee8c63
-- title:
--   Aether Catalog definitions — Combinatorics_CausalintegrationComposition_CausalIntegration_Composition
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.CausalintegrationComposition.CausalIntegration.Composition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/CausalintegrationComposition/CausalIntegration_Composition.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_CausalintegrationCore_CausalIntegration_Core

/-!
# Causal integration: composition

This module previously contained only a stray relative path pointing at a
non-existent file `Shared/CausalIntegration/Composition.lean`.  It is reconstructed
here as the composition theory of the causal operators introduced in
`Shared.CausalintegrationCore.CausalIntegration_Core`.

Main results:

* `CausalIntegration.isCausal_comp` — causal operators are closed under composition,
  so they form a monoid;
* `CausalIntegration.integrate_comp_diff` / `diff_comp_integrate` — integration and
  differencing are mutually inverse *as operators*;
* `CausalIntegration.iteratedIntegrate` and `iteratedIntegrate_isCausal` — the
  iterated running sum is causal;
* `CausalIntegration.integrate_two_eq_weighted` — the second running sum is the
  discrete Abel/Cauchy formula `∑_{k ≤ n} (n + 1 - k) f k`.
-/

namespace CausalIntegration




/-- The `m`-fold running sum. -/
def iteratedIntegrate : ℕ → Op
  | 0 => id
  | m + 1 => integrate ∘ iteratedIntegrate m






end CausalIntegration


