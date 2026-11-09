-- Prove2me | solution 1 for Couret.InterIA.NormalForm.translation_is_affine
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:31:00.870547+00:00
-- url     : https://prove2.me/submissions/38b8ab80-3023-4ec3-9bfa-972edeaeef72

import Definitions.Def_Couret_L4Assembly_154a326d9c14
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_DisjointReduction_b47db5028f89

set_option autoImplicit false
namespace Couret.InterIA.NormalForm
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres



theorem p2m_local_translation_is_affine {n : ℕ} (S T : Finset (ZMod n)) (v : ZMod n)
    (ht : S.image (fun x => x+v)=T) : AffineEquivalent S T := by
  refine ⟨1,v,?_⟩
  simpa using ht







end Couret.InterIA.NormalForm

theorem solution : ∀ {n : Nat} (S T : Finset.{0} (ZMod n)) (v : ZMod n),
  @Eq.{1} (Finset.{0} (ZMod n))
      (@Finset.image.{0, 0} (ZMod n) (ZMod n) (ZMod.decidableEq n)
        (fun x =>
          @HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
            (@instHAdd.{0} (ZMod n)
              (@Distrib.toAdd.{0} (ZMod n)
                (@instDistribOfSemiring.{0} (ZMod n)
                  (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
            x v)
        S)
      T →
    @Couret.InterIA.NormalForm.AffineEquivalent n S T := @_root_.Couret.InterIA.NormalForm.p2m_local_translation_is_affine

