-- Prove2me | Theorems.Thm_Catalog_DerivedFunctors_qShortComplex_shortExact
-- name    : Catalog.DerivedFunctors.qShortComplex_shortExact
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:28:55.581234+00:00
-- url     : https://prove2.me/theorems/4fa2f354-ba9c-4a30-9bca-7f32f6b51814
-- title:
--   The standard injective resolution of `ℤ` is short exact.
-- statement:
--   The standard injective resolution of `ℤ` is short exact.
--
--   ```lean
--   theorem Catalog.DerivedFunctors.qShortComplex_shortExact: qShortComplex.ShortExact := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/DerivedFunctors/Resolutions.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/DerivedFunctors/Resolutions.lean#L116

-- Thm stub generated from Algebra/DerivedFunctors/Resolutions.lean
import Mathlib
import Definitions.Def_Algebra_DerivedFunctors_Resolutions

/-!
# Concrete projective and injective resolutions

This file constructs two concrete resolutions in the category of `ℤ`-modules
(equivalently, abelian groups):

* `Catalog.DerivedFunctors.zmodShortComplex k`: the short exact sequence
  `0 → ℤ --(·k)--> ℤ --(mod k)--> ZMod k → 0`, which is the standard length-one
  free (hence projective) resolution of the cyclic group `ZMod k` for `k ≠ 0`.

These are used in `Algebra.DerivedFunctors.Ext` to compute `Ext`-groups.
-/

universe u

open CategoryTheory Abelian Limits

open Catalog.DerivedFunctors


variable (k : ℕ)

theorem Catalog.DerivedFunctors.qShortComplex_shortExact: qShortComplex.ShortExact := by sorry
