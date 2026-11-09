-- Prove2me | solution 1 for Couret.Certificate.StepValid_sound
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:31:19.91223+00:00
-- url     : https://prove2.me/submissions/fa9d5a0e-f4a0-4dd2-be28-b7dc993e9f47

import Definitions.Def_Couret_BCS4MaskSemantics_c230b02349ef
import Std
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-! Explicit decoding of the historical Python bit positions.
Bit positions follow [1,7,11,13,17,19,23,29], not lexicographic C2 x C4.
All finite facts below are checked by kernel `decide`.
-/
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Couret
namespace Certificate
















































theorem p2m_local_StepValid_sound {s t : EncodedState} {g : Symbol} (h : StepValid s t g) :
    decode t = step mod30Product (decode s) (symbolCode g) := by
  cases s with
  | none => cases t with
    | none => exact False.elim h
    | some t =>
      change State.active (symbolCode t.1) (maskSupport t.2) =
        State.active (symbolCode g) (fun _ => False)
      rw [h.1]
      apply congrArg (State.active (symbolCode g))
      funext u
      exact propext ⟨h.2 u, False.elim⟩
  | some s => cases t with
    | none => exact False.elim h
    | some t =>
      change State.active (symbolCode t.1) (maskSupport t.2) =
        State.active (mul30 (symbolCode s.1) (symbolCode g)) _
      rw [h.1]
      apply congrArg (State.active (mul30 (symbolCode s.1) (symbolCode g)))
      funext u
      exact propext (h.2 u)

end Certificate
end Couret

theorem solution : ∀ {s t : Couret.Certificate.EncodedState} {g : Couret.Certificate.Symbol},
  Couret.Certificate.StepValid s t g →
    @Eq.{1} (Couret.State.{0} Couret.Code30) (Couret.Certificate.decode t)
      (@Couret.step.{0} Couret.Code30 Couret.mod30Product (Couret.Certificate.decode s)
        (Couret.Certificate.symbolCode g)) := @_root_.Couret.Certificate.p2m_local_StepValid_sound

