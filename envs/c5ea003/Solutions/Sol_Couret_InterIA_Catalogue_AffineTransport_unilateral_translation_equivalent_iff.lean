-- Prove2me | solution 1 for Couret.InterIA.Catalogue.AffineTransport.unilateral_translation_equivalent_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:22.880609+00:00
-- url     : https://prove2.me/submissions/e764e461-8f74-4572-9f63-79e98af76ceb

import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
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
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_affine_equivalent_symm
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_affine_equivalent_trans
import Theorems.Thm_Couret_InterIA_NormalForm_translation_is_affine
import Definitions.Def_Couret_AffineParameterControls_321393084939

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.AffineTransport
open Finset Couret.InterIA.NormalForm









theorem p2m_local_unilateral_translation_equivalent_iff {n : ℕ} (S T : Finset (ZMod n)) (t : ZMod n) :
    AffineEquivalent S (T.image (fun z => z+t)) ↔ AffineEquivalent S T := by
  have ht : AffineEquivalent T (T.image (fun z => z+t)) :=
    translation_is_affine T _ t rfl
  constructor
  · intro h
    exact affine_equivalent_trans S _ T h (affine_equivalent_symm T _ ht)
  · intro h
    exact affine_equivalent_trans S T _ h ht



end Couret.InterIA.Catalogue.AffineTransport

theorem solution : ∀ {n : Nat} (S T : Finset.{0} (ZMod n)) (t : ZMod n),
  Iff
    (@Couret.InterIA.NormalForm.AffineEquivalent n S
      (@Finset.image.{0, 0} (ZMod n) (ZMod n) (ZMod.decidableEq n)
        (fun z =>
          @HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
            (@instHAdd.{0} (ZMod n)
              (@Distrib.toAdd.{0} (ZMod n)
                (@instDistribOfSemiring.{0} (ZMod n)
                  (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
            z t)
        T))
    (@Couret.InterIA.NormalForm.AffineEquivalent n S T) := @_root_.Couret.InterIA.Catalogue.AffineTransport.p2m_local_unilateral_translation_equivalent_iff

