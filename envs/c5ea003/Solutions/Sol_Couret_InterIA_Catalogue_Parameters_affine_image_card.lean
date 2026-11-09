-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Parameters.affine_image_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:47:53.989484+00:00
-- url     : https://prove2.me/submissions/79ec2d9d-b575-49a4-ab78-91ba9cdb0ee8

import Definitions.Def_Couret_AffineParameterControls_321393084939
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
import Definitions.Def_Couret_AffineSupportForms_4a272694daca
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Parameters
open Finset Couret.InterIA.Catalogue.Affine Couret.InterIA.Parity

variable {G : Type*} [DecidableEq G]



theorem p2m_local_affine_image_card (n : ℕ) (S : Finset (ZMod n)) (u : (ZMod n)ˣ) (v : ZMod n) :
    (S.image (fun z => (u : ZMod n)*z+v)).card=S.card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb he
  have hh := congrArg (fun z : ZMod n => (↑(u⁻¹) : ZMod n)*z) (add_right_cancel he)
  simpa [← mul_assoc] using hh









end Couret.InterIA.Catalogue.Parameters

theorem solution : ∀ (n : Nat) (S : Finset.{0} (ZMod n))
  (u :
    @Units.{0} (ZMod n)
      (@Semiring.toMonoid.{0} (ZMod n)
        (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))
  (v : ZMod n),
  @Eq.{1} Nat
    (@Finset.card.{0} (ZMod n)
      (@Finset.image.{0, 0} (ZMod n) (ZMod n) (ZMod.decidableEq n)
        (fun z =>
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
              z)
            v)
        S))
    (@Finset.card.{0} (ZMod n) S) := @_root_.Couret.InterIA.Catalogue.Parameters.p2m_local_affine_image_card

