-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Exact.ordered_square_affine_at
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:58.819644+00:00
-- url     : https://prove2.me/submissions/84e6b6ab-9636-4645-a071-24c55f893761

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_unit_affine_injective
import Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Arithmetic Couret.InterIA.Catalogue.Quarter.Ambient
open Couret.InterIA.Catalogue.Quarter.AffineCriterion Couret.InterIA.Catalogue.AffineTransport



theorem p2m_local_ordered_square_affine_at {n : ℕ} (S : Finset (ZMod n))
    (u : (ZMod n)ˣ) (v z : ZMod n) :
    orderedSquare (S.image (fun x => (u : ZMod n)*x+v)) ((u : ZMod n)*z+(v+v))=
      orderedSquare S z := by
  have hf := unit_affine_injective u v
  unfold orderedSquare
  rw [Finset.sum_image (fun a _ b _ he => hf he)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_image (fun a _ b _ he => hf he)]
  apply Finset.sum_congr rfl
  intro b hb
  have he : ((u : ZMod n)*a+v)+((u : ZMod n)*b+v)=(u : ZMod n)*z+(v+v) ↔ a+b=z := by
    rw [show ((u : ZMod n)*a+v)+((u : ZMod n)*b+v)=(u : ZMod n)*(a+b)+(v+v) by ring]
    constructor
    · intro h
      exact (Units.mul_right_inj u).mp (add_right_cancel h)
    · intro h
      rw [h]
  simp only [he]















end Couret.InterIA.Catalogue.Exact

theorem solution : ∀ {n : Nat} (S : Finset.{0} (ZMod n))
  (u :
    @Units.{0} (ZMod n)
      (@Semiring.toMonoid.{0} (ZMod n)
        (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))
  (v z : ZMod n),
  @Eq.{1} Nat
    (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
      (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (ZMod.decidableEq n)
      (@Finset.image.{0, 0} (ZMod n) (ZMod n) (ZMod.decidableEq n)
        (fun x =>
          @HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
            (@instHAdd.{0} (ZMod n)
              (@Distrib.toAdd.{0} (ZMod n)
                (@instDistribOfSemiring.{0} (ZMod n)
                  (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
            (@HMul.hMul.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
              (@instHMul.{0} (ZMod n)
                (@Distrib.toMul.{0} (ZMod n)
                  (@instDistribOfSemiring.{0} (ZMod n)
                    (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
              (@Units.val.{0} (ZMod n)
                (@Semiring.toMonoid.{0} (ZMod n)
                  (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))
                u)
              x)
            v)
        S)
      (@HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
        (@instHAdd.{0} (ZMod n)
          (@Distrib.toAdd.{0} (ZMod n)
            (@instDistribOfSemiring.{0} (ZMod n)
              (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
        (@HMul.hMul.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
          (@instHMul.{0} (ZMod n)
            (@Distrib.toMul.{0} (ZMod n)
              (@instDistribOfSemiring.{0} (ZMod n)
                (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
          (@Units.val.{0} (ZMod n)
            (@Semiring.toMonoid.{0} (ZMod n)
              (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))
            u)
          z)
        (@HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
          (@instHAdd.{0} (ZMod n)
            (@Distrib.toAdd.{0} (ZMod n)
              (@instDistribOfSemiring.{0} (ZMod n)
                (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
          v v)))
    (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
      (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (ZMod.decidableEq n) S z) := @_root_.Couret.InterIA.Catalogue.Exact.p2m_local_ordered_square_affine_at

