-- Prove2me | solution 1 for Couret.InterIA.Cubic.cconv_indicator_left
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:58:16.686457+00:00
-- url     : https://prove2.me/submissions/8d79ac2c-093d-4b9a-a2ff-ff47dcd0c668

import Definitions.Def_Couret_CubicSupport_513df21f9351
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_CubicFourier_396e42df2f8b
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.Cubic
open Finset Couret.InterIA.Parity







theorem p2m_local_cconv_indicator_left {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (g : G → ℂ) (z : G) :
    cconv (complexIndicator S) g z = ∑ x ∈ S, g (z-x) := by
  classical
  have hxy (x y : G) : x+y=z ↔ y=z-x := by
    simp only [eq_sub_iff_add_eq,add_comm]
  calc
    _ = ∑ x : G, if x ∈ S then g (z-x) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hs : x ∈ S
      · simp [complexIndicator,hs,hxy,Finset.sum_ite_eq']
      · simp [complexIndicator,hs]
    _ = ∑ x ∈ S, if x ∈ S then g (z-x) else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro x hx hn
      simp [hn]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [hx]













end Couret.InterIA.Cubic

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : Fintype.{p2m_u_0} G]
  [inst_2 : DecidableEq.{p2m_u_0 + 1} G] (S : Finset.{p2m_u_0} G) (g : G → Complex) (z : G),
  @Eq.{1} Complex
    (@Couret.InterIA.Cubic.cconv.{p2m_u_0} G inst inst_1 inst_2
      (@Couret.InterIA.Cubic.complexIndicator.{p2m_u_0} G inst_2 S) g z)
    (@Finset.sum.{p2m_u_0, 0} G Complex
      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
              (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Complex
                (@NormedCommRing.toNonUnitalNormedCommRing.{0} Complex
                  (@NormedField.toNormedCommRing.{0} Complex Complex.instNormedField)))))))
      S fun x =>
      g
        (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHSub.{p2m_u_0} G
            (@SubNegMonoid.toSub.{p2m_u_0} G
              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
          z x)) := @_root_.Couret.InterIA.Cubic.p2m_local_cconv_indicator_left

