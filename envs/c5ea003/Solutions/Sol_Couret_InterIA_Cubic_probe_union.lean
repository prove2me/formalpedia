-- Prove2me | solution 1 for Couret.InterIA.Cubic.probe_union
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:05:25.736402+00:00
-- url     : https://prove2.me/submissions/808f9a6f-ad77-49cf-aed4-aea3d4297498

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

















theorem p2m_local_probe_union {G : Type*} [AddCommGroup G] [DecidableEq G]
    (r : G → ℝ) (S T : Finset G) (hd : Disjoint S T) :
    probe r (S ∪ T)=probe r S+probe r T := by
  funext z
  exact Finset.sum_union hd



end Couret.InterIA.Cubic

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (r : G → Real)
  (S T : Finset.{p2m_u_0} G),
  @Disjoint.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.partialOrder.{p2m_u_0} G) (@Finset.instOrderBot.{p2m_u_0} G) S T →
    @Eq.{p2m_u_0 + 1} (G → Real)
      (@Couret.InterIA.Cubic.probe.{p2m_u_0} G inst inst_1 r
        (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instUnion.{p2m_u_0} G inst_1) S T))
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} (G → Real) (G → Real) (G → Real)
        (@instHAdd.{p2m_u_0} (G → Real) (@Pi.instAdd.{p2m_u_0, 0} G (fun a => Real) fun i => Real.instAdd))
        (@Couret.InterIA.Cubic.probe.{p2m_u_0} G inst inst_1 r S)
        (@Couret.InterIA.Cubic.probe.{p2m_u_0} G inst inst_1 r T)) := @_root_.Couret.InterIA.Cubic.p2m_local_probe_union

