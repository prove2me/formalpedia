-- Prove2me | solution 1 for Couret.InterIA.Cubic.cube_eq_probe
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:04:51.293889+00:00
-- url     : https://prove2.me/submissions/ed67463d-79a6-4d09-90b2-c0a76fb8d9d9

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



















theorem p2m_local_cube_eq_probe {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S T : Finset G) (hs : ∀ z, orderedSquare S z=orderedSquare T z) :
    (fun z => (orderedCube T z : ℝ)) = probe (fun z => (orderedSquare S z : ℝ)) T := by
  funext z
  simp only [orderedCube,probe,Nat.cast_sum,hs]

end Couret.InterIA.Cubic

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (S T : Finset.{p2m_u_0} G),
  (∀ (z : G),
      @Eq.{1} Nat (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1 S z)
        (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1 T z)) →
    @Eq.{p2m_u_0 + 1} (G → Real)
      (fun z => @Nat.cast.{0} Real Real.instNatCast (@Couret.InterIA.Cubic.orderedCube.{p2m_u_0} G inst inst_1 T z))
      (@Couret.InterIA.Cubic.probe.{p2m_u_0} G inst inst_1
        (fun z =>
          @Nat.cast.{0} Real Real.instNatCast (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1 S z))
        T) := @_root_.Couret.InterIA.Cubic.p2m_local_cube_eq_probe

