-- Prove2me | Theorems.Thm_CausalIntegration_integrate_two_eq_weighted
-- name    : CausalIntegration.integrate_two_eq_weighted
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:03:50.804383+00:00
-- url     : https://prove2.me/theorems/2dd60fbc-fce0-43f7-b1dc-c290a6b9708a
-- title:
--   The double running sum is the weighted single sum
-- statement:
--   The double running sum is the weighted single sum
--   `(∫²f)(n) = ∑_{k ≤ n} (n + 1 - k) · f k`, the discrete Abel summation formula.
--
--   ```lean
--   theorem CausalIntegration.integrate_two_eq_weighted(f : Signal) (n : ℕ) :
--       iteratedIntegrate 2 f n = ∑ k ∈ Finset.range (n + 1), ((n + 1 - k : ℕ) : ℝ) * f k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/CausalintegrationComposition/CausalIntegration_Composition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/CausalintegrationComposition/CausalIntegration_Composition.lean#L57

-- Thm stub generated from Combinatorics/CausalintegrationComposition/CausalIntegration_Composition.lean
import Mathlib
import Definitions.Def_Combinatorics_CausalintegrationComposition_CausalIntegration_Composition
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

open CausalIntegration

theorem CausalIntegration.integrate_two_eq_weighted(f : Signal) (n : ℕ) :
    iteratedIntegrate 2 f n = ∑ k ∈ Finset.range (n + 1), ((n + 1 - k : ℕ) : ℝ) * f k := by sorry
