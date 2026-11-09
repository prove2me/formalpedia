-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.AffineCriterion.unit_affine_injective
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:32:03.773784+00:00
-- url     : https://prove2.me/submissions/1167db93-f205-41e3-adf2-aa24fa81b31e

import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
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
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm

theorem p2m_local_unit_affine_injective {n : ℕ} (u : (ZMod n)ˣ) (v : ZMod n) :
    Function.Injective (fun z : ZMod n => (u : ZMod n)*z+v) := by
  intro a b hab
  exact (Units.mul_right_inj u).mp (add_right_cancel hab)











end Couret.InterIA.Catalogue.Quarter.AffineCriterion

theorem solution : ∀ {n : Nat}
  (u :
    @Units.{0} (ZMod n)
      (@Semiring.toMonoid.{0} (ZMod n)
        (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))
  (v : ZMod n),
  @Function.Injective.{1, 1} (ZMod n) (ZMod n) fun z =>
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
      v := @_root_.Couret.InterIA.Catalogue.Quarter.AffineCriterion.p2m_local_unit_affine_injective

