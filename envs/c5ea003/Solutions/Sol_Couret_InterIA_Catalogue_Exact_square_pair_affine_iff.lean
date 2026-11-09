-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Exact.square_pair_affine_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:57:55.822363+00:00
-- url     : https://prove2.me/submissions/dda343eb-249a-4eac-a4ac-8701a66689a2

import Definitions.Def_Couret_ReferenceCatalogueConverse_0cbe68a31344
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_ordered_square_affine_at
import Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Arithmetic Couret.InterIA.Catalogue.Quarter.Ambient
open Couret.InterIA.Catalogue.Quarter.AffineCriterion Couret.InterIA.Catalogue.AffineTransport





theorem p2m_local_square_pair_affine_iff {n : ℕ} (S T : Finset (ZMod n))
    (u : (ZMod n)ˣ) (v : ZMod n) :
    (∀ z, orderedSquare (S.image (fun x => (u : ZMod n)*x+v)) z=
      orderedSquare (T.image (fun x => (u : ZMod n)*x+v)) z) ↔
      ∀ z, orderedSquare S z=orderedSquare T z := by
  constructor
  · intro h z
    rw [← ordered_square_affine_at S u v z,← ordered_square_affine_at T u v z]
    exact h _
  · intro h w
    let z := (↑(u⁻¹) : ZMod n)*(w-(v+v))
    have hz : (u : ZMod n)*z+(v+v)=w := by
      dsimp [z]
      calc _=((u : ZMod n)*(↑(u⁻¹) : ZMod n))*(w-(v+v))+(v+v) := by ring
           _=w := by simp
    rw [← hz,ordered_square_affine_at,ordered_square_affine_at]
    exact h z













end Couret.InterIA.Catalogue.Exact

theorem solution : ∀ {n : Nat} (S T : Finset.{0} (ZMod n))
  (u :
    @Units.{0} (ZMod n)
      (@Semiring.toMonoid.{0} (ZMod n)
        (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))
  (v : ZMod n),
  Iff
    (∀ (z : ZMod n),
      @Eq.{1} Nat
        (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
          (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (ZMod.decidableEq n)
          (@Finset.image.{0, 0} (ZMod n) (ZMod n) (ZMod.decidableEq n)
            (fun x =>
              @HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                (@instHAdd.{0} (ZMod n)
                  (@Distrib.toAdd.{0} (ZMod n)
                    (@instDistribOfSemiring.{0} (ZMod n)
                      (@CommSemiring.toSemiring.{0} (ZMod n)
                        (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                (@HMul.hMul.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                  (@instHMul.{0} (ZMod n)
                    (@Distrib.toMul.{0} (ZMod n)
                      (@instDistribOfSemiring.{0} (ZMod n)
                        (@CommSemiring.toSemiring.{0} (ZMod n)
                          (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                  (@Units.val.{0} (ZMod n)
                    (@Semiring.toMonoid.{0} (ZMod n)
                      (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))
                    u)
                  x)
                v)
            S)
          z)
        (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
          (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (ZMod.decidableEq n)
          (@Finset.image.{0, 0} (ZMod n) (ZMod n) (ZMod.decidableEq n)
            (fun x =>
              @HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                (@instHAdd.{0} (ZMod n)
                  (@Distrib.toAdd.{0} (ZMod n)
                    (@instDistribOfSemiring.{0} (ZMod n)
                      (@CommSemiring.toSemiring.{0} (ZMod n)
                        (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                (@HMul.hMul.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                  (@instHMul.{0} (ZMod n)
                    (@Distrib.toMul.{0} (ZMod n)
                      (@instDistribOfSemiring.{0} (ZMod n)
                        (@CommSemiring.toSemiring.{0} (ZMod n)
                          (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                  (@Units.val.{0} (ZMod n)
                    (@Semiring.toMonoid.{0} (ZMod n)
                      (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))
                    u)
                  x)
                v)
            T)
          z))
    (∀ (z : ZMod n),
      @Eq.{1} Nat
        (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
          (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (ZMod.decidableEq n) S
          z)
        (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
          (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (ZMod.decidableEq n) T
          z)) := @_root_.Couret.InterIA.Catalogue.Exact.p2m_local_square_pair_affine_iff

