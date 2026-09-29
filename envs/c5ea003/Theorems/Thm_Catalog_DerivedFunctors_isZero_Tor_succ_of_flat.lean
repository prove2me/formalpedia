-- Prove2me | Theorems.Thm_Catalog_DerivedFunctors_isZero_Tor_succ_of_flat
-- name    : Catalog.DerivedFunctors.isZero_Tor_succ_of_flat
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:43:37.116001+00:00
-- url     : https://prove2.me/theorems/6d40a1a4-8f9b-4751-933e-21e45337ba74
-- title:
--   Higher Tor against a flat module vanishes.
-- statement:
--   **Higher Tor against a flat module vanishes.**
--
--   ```lean
--   theorem Catalog.DerivedFunctors.isZero_Tor_succ_of_flat(G : ModuleCat.{u} R) [Module.Flat R G] (M : ModuleCat.{u} R)
--       (n : ℕ) : IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj G).obj M) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/DerivedFunctors/Tor.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/DerivedFunctors/Tor.lean#L33

-- Thm stub generated from Algebra/DerivedFunctors/Tor.lean
import Mathlib

/-!
# The Tor functors: degree zero and vanishing for flat modules

`CategoryTheory.Tor C n` is the `n`-th left derived functor of the tensor product (derived in the
second variable). This file develops two basic facts about it in the category of modules:

* `Catalog.DerivedFunctors.torZeroIso`: `Tor₀(G, M) ≅ G ⊗ M`;
* `Catalog.DerivedFunctors.isZero_Tor_succ_of_flat`: **all higher Tor groups against a flat module
  vanish**, `Torₙ₊₁(G, M) = 0` whenever `G` is flat. The proof computes the left derived functor
  along an arbitrary projective resolution `P → M`, and uses that tensoring with a flat module is
  exact, hence commutes with homology; since `P` is exact in positive degrees the result follows.
* `Catalog.DerivedFunctors.not_flat_of_Tor_ne_zero`: the contrapositive, a nonvanishing higher Tor
  group is an obstruction to flatness.

Concrete consequences over `ℤ` are recorded at the end: all higher Tor groups against `ℚ` (a
torsion-free, hence flat, `ℤ`-module) and against `ℤ` itself vanish.
-/

universe u

open CategoryTheory MonoidalCategory Limits


variable {R : Type u} [CommRing R]

theorem Catalog.DerivedFunctors.isZero_Tor_succ_of_flat(G : ModuleCat.{u} R) [Module.Flat R G] (M : ModuleCat.{u} R)
    (n : ℕ) : IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj G).obj M) := by sorry
