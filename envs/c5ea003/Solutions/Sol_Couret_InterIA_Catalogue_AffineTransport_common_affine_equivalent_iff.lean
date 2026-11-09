-- Prove2me | solution 1 for Couret.InterIA.Catalogue.AffineTransport.common_affine_equivalent_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:34.30206+00:00
-- url     : https://prove2.me/submissions/028dbe6a-c0bf-4b07-ba7e-fa2e03e03494

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
import Definitions.Def_Couret_AffineParameterControls_321393084939

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.AffineTransport
open Finset Couret.InterIA.NormalForm





theorem affine_equivalent_image {n : ℕ} (S : Finset (ZMod n))
    (u : (ZMod n)ˣ) (v : ZMod n) :
    AffineEquivalent S (S.image (fun z => (u : ZMod n)*z+v)) := ⟨u,v,rfl⟩

theorem p2m_local_common_affine_equivalent_iff {n : ℕ} (S T : Finset (ZMod n))
    (u : (ZMod n)ˣ) (v : ZMod n) :
    AffineEquivalent (S.image (fun z => (u : ZMod n)*z+v))
      (T.image (fun z => (u : ZMod n)*z+v)) ↔ AffineEquivalent S T := by
  let S' := S.image (fun z => (u : ZMod n)*z+v)
  let T' := T.image (fun z => (u : ZMod n)*z+v)
  have hs := affine_equivalent_image S u v
  have ht := affine_equivalent_image T u v
  constructor
  · intro h
    exact affine_equivalent_trans S T' T (affine_equivalent_trans S S' T' hs h)
      (affine_equivalent_symm T T' ht)
  · intro h
    exact affine_equivalent_trans S' T T' (affine_equivalent_trans S' S T
      (affine_equivalent_symm S S' hs) h) ht





end Couret.InterIA.Catalogue.AffineTransport

theorem solution : ∀ {n : Nat} (S T : Finset.{0} (ZMod n))
  (u :
    @Units.{0} (ZMod n)
      (@Semiring.toMonoid.{0} (ZMod n)
        (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))
  (v : ZMod n),
  Iff
    (@Couret.InterIA.NormalForm.AffineEquivalent n
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
        T))
    (@Couret.InterIA.NormalForm.AffineEquivalent n S T) := @_root_.Couret.InterIA.Catalogue.AffineTransport.p2m_local_common_affine_equivalent_iff

