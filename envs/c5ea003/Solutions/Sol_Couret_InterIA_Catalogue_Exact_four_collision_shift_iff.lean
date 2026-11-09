-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Exact.four_collision_shift_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:05:16.902555+00:00
-- url     : https://prove2.me/submissions/9477e8b5-5fc8-4587-b8b0-329a2a341ad5

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
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_unilateral_translation_equivalent_iff
import Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Arithmetic Couret.InterIA.Catalogue.Quarter.Ambient
open Couret.InterIA.Catalogue.Quarter.AffineCriterion Couret.InterIA.Catalogue.AffineTransport











theorem p2m_local_four_collision_shift_iff {n : ℕ} (S T : Finset (ZMod n)) (t : ZMod n)
    (ht : t+t=0) : FourCollision S (T.image (fun z => z+t)) ↔ FourCollision S T := by
  have hc : (T.image (fun z => z+t)).card=T.card :=
    Finset.card_image_of_injective _ (fun _ _ he => add_right_cancel he)
  simp only [FourCollision,hc,Couret.InterIA.Translation.two_torsion_translation_preserves_square T t ht,
    unilateral_translation_equivalent_iff]







end Couret.InterIA.Catalogue.Exact

theorem solution : ∀ {n : Nat} (S T : Finset.{0} (ZMod n)) (t : ZMod n),
  @Eq.{1} (ZMod n)
      (@HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
        (@instHAdd.{0} (ZMod n)
          (@Distrib.toAdd.{0} (ZMod n)
            (@instDistribOfSemiring.{0} (ZMod n)
              (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
        t t)
      (@OfNat.ofNat.{0} (ZMod n) (nat_lit 0)
        (@Zero.toOfNat0.{0} (ZMod n)
          (@MulZeroClass.toZero.{0} (ZMod n)
            (@instMulZeroClassOfSemiring.{0} (ZMod n)
              (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))) →
    Iff
      (@Couret.InterIA.Catalogue.Exact.FourCollision n S
        (@Finset.image.{0, 0} (ZMod n) (ZMod n) (ZMod.decidableEq n)
          (fun z =>
            @HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
              (@instHAdd.{0} (ZMod n)
                (@Distrib.toAdd.{0} (ZMod n)
                  (@instDistribOfSemiring.{0} (ZMod n)
                    (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
              z t)
          T))
      (@Couret.InterIA.Catalogue.Exact.FourCollision n S T) := @_root_.Couret.InterIA.Catalogue.Exact.p2m_local_four_collision_shift_iff

