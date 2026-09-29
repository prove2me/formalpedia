-- Prove2me | Theorems.Thm_BerggrenFiniteSpectral_berggrenInvGenAction_injective
-- name    : BerggrenFiniteSpectral.berggrenInvGenAction_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-16T20:30:08.932061+00:00
-- url     : https://prove2.me/theorems/a0449d11-41fa-4278-ab6e-635b316e5dd5
-- title:
--   The inverse generator action is injective.
-- statement:
--   The inverse generator action is injective.
--
--   ```lean
--   theorem BerggrenFiniteSpectral.berggrenInvGenAction_injective(q : ℕ) [NeZero q] (i : Fin 3) :
--       Function.Injective (berggrenInvGenAction q i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/BerggrenFiniteSpectral.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/BerggrenFiniteSpectral.lean#L224

-- Thm stub generated from Bridges/BerggrenFiniteSpectral.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenFiniteSpectral

/-!
# Berggren Spectral Theory on Finite Quotients

This file develops the spectral theory of the Berggren averaging operator
on the isotropic cone of the Lorentzian quadratic form Q(x,y,z) = x² + y² - z²
reduced modulo odd primes q.

## Main Results

### Algebraic Infrastructure (over ℤ)
* `berggrenGen_preserves_metric` — Each generator preserves the Lorentz metric MᵀQM = Q.
* `berggrenGen_mul_inv` / `berggrenInvGen_mul_gen` — Verified inverse pairs.
* `berggren_sum_lorentz_identity` — SᵀQS = diag(1,1,-9), the key amplification identity.

### Mod-q Reduction
* `quadFormMod_preserved_by_gen` — Generators preserve the quadratic form mod q.
* `berggrenGenAction` — The action on the isotropic cone is well-defined.
* `berggrenGenAction_bijective` — Each generator acts by bijection on the finite cone.

### Operator Theory
* `berggren_constants_eigenvalue_one` — Constants are eigenvectors with eigenvalue 1.
* `berggren_mean_zero_invariant` — The averaging operator preserves mean-zero functions.
* `berggren_averaging_sum_preserved` — Total sums are preserved by the operator.
-/

set_option maxHeartbeats 800000

open Matrix Finset BigOperators

open BerggrenFiniteSpectral

/-! ## §1. Core Definitions over ℤ -/






/-! ## §2. Algebraic Identities -/









/-! ## §3. Quadratic Form Preservation over ℤ -/



/-! ## §4. Mod-q Definitions and Form Preservation -/









/-! ## §5. Isotropic Cone and Group Action -/

theorem BerggrenFiniteSpectral.berggrenInvGenAction_injective(q : ℕ) [NeZero q] (i : Fin 3) :
    Function.Injective (berggrenInvGenAction q i) := by sorry
