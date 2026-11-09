-- Prove2me | solution 1 for CouretOaiBridge01.fixedModulusNoGain
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:02:25.20396+00:00
-- url     : https://prove2.me/submissions/3eb95520-f484-4b9d-b2fe-b632e9772ccd

import Definitions.Def_Couret_BRIDGE01_A2_FixedModulusNoGain_7a86db44985c
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Asymptotics
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_CouretOaiBridge01_isBigO_comp_continuousLinearEquiv_iff
import Definitions.Def_Couret_BRIDGE01_A1_U30KernelInverse_5560f1024274
attribute [local instance] CouretOaiBridge01.u30AlgRNormedAddCommGroup
attribute [local instance] CouretOaiBridge01.u30AlgRNormedSpace

/-!
# BRIDGE01 / A2: fixed-modulus no-gain on the full real coefficient vector

RESEARCH BRANCH ONLY — NO RH CLAIM — NO NOVELTY CLAIM.
The norm is the sup norm transported from all eight coefficient coordinates.
Completeness is used only for the real scalar field in Mathlib's continuity API.
-/

open Filter
open Asymptotics

namespace CouretOaiBridge01

noncomputable section







































@[simp] theorem tauRMulContinuousLinearEquiv_apply (x : U30AlgR) :
    tauRMulContinuousLinearEquiv x = tauR * x := by
  rfl

/--
A2: fixed convolution by the Couret kernel preserves every Big-O class of the full real
coefficient state.
-/
theorem p2m_local_fixedModulusNoGain
    {G α : Type*}
    [SeminormedAddCommGroup G]
    (F : α → U30AlgR)
    (g : α → G)
    (l : Filter α) :
    (fun x => tauR * F x) =O[l] g ↔ F =O[l] g := by
  simpa only [tauRMulContinuousLinearEquiv_apply] using
    isBigO_comp_continuousLinearEquiv_iff tauRMulContinuousLinearEquiv F g l

end

end CouretOaiBridge01

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} {α : Type p2m_u_1} [inst : SeminormedAddCommGroup.{p2m_u_0} G] (F : α → CouretOaiBridge01.U30AlgR)
  (g : α → G) (l : Filter.{p2m_u_1} α),
  Iff
    (@Asymptotics.IsBigO.{p2m_u_1, 0, p2m_u_0} α CouretOaiBridge01.U30AlgR G
      (@NormedAddCommGroup.toNorm.{0} CouretOaiBridge01.U30AlgR CouretOaiBridge01.u30AlgRNormedAddCommGroup)
      (@SeminormedAddCommGroup.toNorm.{p2m_u_0} G inst) l
      (fun x =>
        @HMul.hMul.{0, 0, 0} CouretOaiBridge01.U30AlgR CouretOaiBridge01.U30AlgR CouretOaiBridge01.U30AlgR
          (@instHMul.{0} CouretOaiBridge01.U30AlgR
            (@MonoidAlgebra.instMul.{0, 0} Real CouretOaiBridge01.U30 Real.semiring
              (@Units.instMul.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                (@Semiring.toMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                  (@CommSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                    (@CommRing.toCommSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                      (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))))))))
          CouretOaiBridge01.tauR (F x))
      g)
    (@Asymptotics.IsBigO.{p2m_u_1, 0, p2m_u_0} α CouretOaiBridge01.U30AlgR G
      (@NormedAddCommGroup.toNorm.{0} CouretOaiBridge01.U30AlgR CouretOaiBridge01.u30AlgRNormedAddCommGroup)
      (@SeminormedAddCommGroup.toNorm.{p2m_u_0} G inst) l F g) := @_root_.CouretOaiBridge01.p2m_local_fixedModulusNoGain

