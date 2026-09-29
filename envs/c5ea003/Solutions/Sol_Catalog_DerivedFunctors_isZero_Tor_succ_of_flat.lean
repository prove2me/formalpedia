-- Prove2me | solution 1 for Catalog.DerivedFunctors.isZero_Tor_succ_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T18:47:05.09202+00:00
-- url     : https://prove2.me/submissions/a9883971-137d-47b5-86fe-a562f3f6902e

-- Sol generated from Algebra/DerivedFunctors/Tor.lean
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









theorem solution(G : ModuleCat.{u} R) [Module.Flat R G] (M : ModuleCat.{u} R)
    (n : ℕ) : IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj G).obj M) := by
  let P := ProjectiveResolution.of M
  let F := (tensoringLeft (ModuleCat.{u} R)).obj G
  have h1 : ((F.leftDerived (n + 1)).obj M) ≅
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology (n + 1) :=
    P.isoLeftDerivedObj F (n + 1)
  have h2 : (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology (n + 1)) ≅
      F.obj (P.complex.homology (n + 1)) := (P.complex.sc (n + 1)).mapHomologyIso F
  have h3 : IsZero (P.complex.homology (n + 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact P.complex_exactAt_succ n
  exact (Functor.map_isZero F h3).of_iso (h1 ≪≫ h2)
