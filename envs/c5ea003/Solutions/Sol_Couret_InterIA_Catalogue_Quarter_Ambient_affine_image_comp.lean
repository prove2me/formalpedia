-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Ambient.affine_image_comp
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:54.469183+00:00
-- url     : https://prove2.me/submissions/d331ee9c-6606-4fe2-9aaa-651ea8c096d7

import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347
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
import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Ambient
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Primitive







theorem p2m_local_affine_image_comp {n : ℕ} (S : Finset (ZMod n))
    (u a : (ZMod n)ˣ) (v b : ZMod n) :
    (S.image (fun z => (u : ZMod n)*z+v)).image (fun z => (a : ZMod n)*z+b)=
      S.image (fun z => (↑(a*u) : ZMod n)*z+((a : ZMod n)*v+b)) := by
  rw [image_image]
  apply Finset.image_congr
  intro z hz
  simp only [Function.comp_apply,Units.val_mul]
  ring

end Couret.InterIA.Catalogue.Quarter.Ambient

theorem solution : ∀ {n : Nat} (S : Finset.{0} (ZMod n))
  (u a :
    @Units.{0} (ZMod n)
      (@Semiring.toMonoid.{0} (ZMod n)
        (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))
  (v b : ZMod n),
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
              a)
            z)
          b)
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
              (@HMul.hMul.{0, 0, 0}
                (@Units.{0} (ZMod n)
                  (@Semiring.toMonoid.{0} (ZMod n)
                    (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))
                (@Units.{0} (ZMod n)
                  (@Semiring.toMonoid.{0} (ZMod n)
                    (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))
                (@Units.{0} (ZMod n)
                  (@Semiring.toMonoid.{0} (ZMod n)
                    (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))
                (@instHMul.{0}
                  (@Units.{0} (ZMod n)
                    (@Semiring.toMonoid.{0} (ZMod n)
                      (@CommSemiring.toSemiring.{0} (ZMod n)
                        (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))
                  (@Units.instMul.{0} (ZMod n)
                    (@Semiring.toMonoid.{0} (ZMod n)
                      (@CommSemiring.toSemiring.{0} (ZMod n)
                        (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
                a u))
            z)
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
                a)
              v)
            b))
      S) := @_root_.Couret.InterIA.Catalogue.Quarter.Ambient.p2m_local_affine_image_comp

