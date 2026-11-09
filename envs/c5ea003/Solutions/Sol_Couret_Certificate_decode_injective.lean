-- Prove2me | solution 1 for Couret.Certificate.decode_injective
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:37:01.946671+00:00
-- url     : https://prove2.me/submissions/5b80bf82-fd25-497a-8fa3-f72d3c3d83db

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















theorem code_symbol : ∀ g : Symbol, codeSymbol (symbolCode g) = g := by decide


theorem symbolCode_injective {a b : Symbol} (h : symbolCode a = symbolCode b) :
    a = b := by
  have he := congrArg codeSymbol h
  simpa only [code_symbol] using he





theorem encode_contains : ∀ m : Mask, encodeBits (contains m) = m.val := by decide





theorem maskSupport_injective {m n : Mask} (h : maskSupport m = maskSupport n) :
    m = n := by
  have hb : contains m = contains n := by
    funext a
    have he := congrFun h (symbolCode a)
    change (contains m (codeSymbol (symbolCode a)) = true) =
      (contains n (codeSymbol (symbolCode a)) = true) at he
    rw [code_symbol] at he
    cases hm : contains m a <;> cases hn : contains n a <;> simp_all
  apply Fin.ext
  have he := congrArg encodeBits hb
  simpa only [encode_contains] using he



theorem p2m_local_decode_injective {a b : EncodedState} (h : decode a = decode b) : a = b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases h
  | some a => cases b with
    | none => cases h
    | some b =>
      have he := State.active.inj h
      have hr : a.1 = b.1 := symbolCode_injective he.1
      have hm : a.2 = b.2 := maskSupport_injective he.2
      exact congrArg some (Prod.ext hr hm)















end Certificate
end Couret

theorem solution : ∀ {a b : Couret.Certificate.EncodedState},
  @Eq.{1} (Couret.State.{0} Couret.Code30) (Couret.Certificate.decode a) (Couret.Certificate.decode b) →
    @Eq.{1} Couret.Certificate.EncodedState a b := @_root_.Couret.Certificate.p2m_local_decode_injective

