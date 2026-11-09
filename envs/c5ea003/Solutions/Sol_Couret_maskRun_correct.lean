-- Prove2me | solution 1 for Couret.maskRun_correct
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:05:48.130754+00:00
-- url     : https://prove2.me/submissions/b04ea1c1-152d-4a42-886e-424770dc0c37

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Theorems.Thm_Couret_maskSupport_or
import Theorems.Thm_Couret_maskSupport_singleton
import Theorems.Thm_Couret_maskSupport_zero
import Theorems.Thm_Couret_run_correct
import Theorems.Thm_Couret_shiftMask_support
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret















































theorem nextMask_support (r g u : Code30) (mask : Nat) :
    maskSupport (nextMask r mask g) u ↔
      maskSupport mask u ∨ (∃ v, maskSupport mask v ∧ mul30 g v = u) ∨
        u = r ∨ u = g := by
  simp only [nextMask, maskSupport_or, shiftMask_support, maskSupport_singleton]
  simp only [or_assoc]













theorem maskStep_simulates (s : MaskState) (g : Code30) :
    decodeMaskState (maskStep s g) = step mod30Product (decodeMaskState s) g := by
  cases s with
  | initial =>
    apply congrArg (State.active g)
    funext u
    exact propext ⟨maskSupport_zero u, False.elim⟩
  | active r mask =>
    apply congrArg (State.active (mul30 r g))
    funext u
    exact propext (nextMask_support r g u mask)





theorem maskRun_simulates (w : Word Code30) :
    decodeMaskState (maskRun w) = run mod30Product w := by
  induction w with
  | empty => rfl
  | snoc w g ih =>
    change decodeMaskState (maskStep (maskRun w) g) = step mod30Product (run mod30Product w) g
    rw [maskStep_simulates, ih]

theorem p2m_local_maskRun_correct (w : Word Code30) :
    decodeMaskState (maskRun w) = semanticState mod30Product w :=
  (maskRun_simulates w).trans (run_correct mod30Product w)













end Couret


theorem solution : ∀ (w : Couret.Word.{0} Couret.Code30),
  @Eq.{1} (Couret.State.{0} Couret.Code30) (Couret.decodeMaskState (Couret.maskRun w))
    (@Couret.semanticState.{0} Couret.Code30 Couret.mod30Product w) := @_root_.Couret.p2m_local_maskRun_correct

