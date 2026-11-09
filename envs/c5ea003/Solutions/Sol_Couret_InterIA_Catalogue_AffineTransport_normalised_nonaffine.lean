-- Prove2me | solution 1 for Couret.InterIA.Catalogue.AffineTransport.normalised_nonaffine
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:48:54.192237+00:00
-- url     : https://prove2.me/submissions/f38e5ab9-314a-440d-9c27-ef29884e1dae

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
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_common_affine_equivalent_iff
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_unilateral_translation_equivalent_iff
import Definitions.Def_Couret_AffineParameterControls_321393084939

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.AffineTransport
open Finset Couret.InterIA.NormalForm











theorem p2m_local_normalised_nonaffine {n : ℕ} (S T A B : Finset (ZMod n))
    (u : (ZMod n)ˣ) (v t : ZMod n)
    (hS : S.image (fun z => (u : ZMod n)*z+v)=A)
    (hT : (T.image (fun z => z+t)).image (fun z => (u : ZMod n)*z+v)=B)
    (h : ¬ AffineEquivalent S T) : ¬ AffineEquivalent A B := by
  rw [← hS,← hT]
  intro he
  exact h ((unilateral_translation_equivalent_iff S T t).mp
    ((common_affine_equivalent_iff S (T.image (fun z => z+t)) u v).mp he))

end Couret.InterIA.Catalogue.AffineTransport

theorem solution : ∀ {n : Nat} (S T A B : Finset.{0} (ZMod n))
  (u :
    @Units.{0} (ZMod n)
      (@Semiring.toMonoid.{0} (ZMod n)
        (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))
  (v t : ZMod n),
  @Eq.{1} (Finset.{0} (ZMod n))
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
        S)
      A →
    @Eq.{1} (Finset.{0} (ZMod n))
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
                      (@CommSemiring.toSemiring.{0} (ZMod n)
                        (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                (@Units.val.{0} (ZMod n)
                  (@Semiring.toMonoid.{0} (ZMod n)
                    (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))
                  u)
                z)
              v)
          (@Finset.image.{0, 0} (ZMod n) (ZMod n) (ZMod.decidableEq n)
            (fun z =>
              @HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
                (@instHAdd.{0} (ZMod n)
                  (@Distrib.toAdd.{0} (ZMod n)
                    (@instDistribOfSemiring.{0} (ZMod n)
                      (@CommSemiring.toSemiring.{0} (ZMod n)
                        (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                z t)
            T))
        B →
      Not (@Couret.InterIA.NormalForm.AffineEquivalent n S T) → Not (@Couret.InterIA.NormalForm.AffineEquivalent n A B) := @_root_.Couret.InterIA.Catalogue.AffineTransport.p2m_local_normalised_nonaffine

