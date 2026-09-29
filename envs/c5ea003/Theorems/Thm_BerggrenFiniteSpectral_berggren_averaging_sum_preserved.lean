-- Prove2me | Theorems.Thm_BerggrenFiniteSpectral_berggren_averaging_sum_preserved
-- name    : BerggrenFiniteSpectral.berggren_averaging_sum_preserved
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-16T20:30:28.477642+00:00
-- url     : https://prove2.me/theorems/e7d8a233-9706-4f56-9f97-26a2250e3a09
-- title:
--   T_q preserves the total sum of f over the isotropic cone.
-- statement:
--   T_q preserves the total sum of f over the isotropic cone.
--
--   ```lean
--   theorem BerggrenFiniteSpectral.berggren_averaging_sum_preserved(q : ℕ) [NeZero q]
--       [Fintype (IsotropicNonzero q)] [DecidableEq (IsotropicNonzero q)]
--       (f : IsotropicNonzero q → ℂ) :
--       ∑ x, berggrenAveragingOp q f x = ∑ x, f x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/BerggrenFiniteSpectral.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/BerggrenFiniteSpectral.lean#L301

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









/-! ## §6. Averaging Operator -/



/-! ## §7. Constants are Eigenvectors -/



/-! ## §8. Mean-Zero Invariance -/

theorem BerggrenFiniteSpectral.berggren_averaging_sum_preserved(q : ℕ) [NeZero q]
    [Fintype (IsotropicNonzero q)] [DecidableEq (IsotropicNonzero q)]
    (f : IsotropicNonzero q → ℂ) :
    ∑ x, berggrenAveragingOp q f x = ∑ x, f x := by sorry
