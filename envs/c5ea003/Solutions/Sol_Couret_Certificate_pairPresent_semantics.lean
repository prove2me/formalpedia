-- Prove2me | solution 1 for Couret.Certificate.pairPresent_semantics
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:37:34.754285+00:00
-- url     : https://prove2.me/submissions/239140d5-7e12-45e3-a5d8-9fbd073e2838

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


























theorem p2m_local_pairPresent_semantics (r : Symbol) (m : Mask) (a b : Symbol) :
    pairPresent (some (r,m)) a b = true ↔
      maskSupport m (symbolCode a) ∧ maskSupport m (symbolCode b) ∧
      a.val ≤ b.val ∧ mul30 (symbolCode a) (symbolCode b) = symbolCode r := by
  simp [pairPresent, maskSupport, code_symbol, Bool.and_eq_true, and_assoc]







end Certificate
end Couret

theorem solution : ∀ (r : Couret.Certificate.Symbol) (m : Couret.Certificate.Mask) (a b : Couret.Certificate.Symbol),
  Iff
    (@Eq.{1} Bool
      (Couret.Certificate.pairPresent
        (@Option.some.{0} (Prod.{0, 0} Couret.Certificate.Symbol Couret.Certificate.Mask)
          (@Prod.mk.{0, 0} Couret.Certificate.Symbol Couret.Certificate.Mask r m))
        a b)
      Bool.true)
    (And (Couret.Certificate.maskSupport m (Couret.Certificate.symbolCode a))
      (And (Couret.Certificate.maskSupport m (Couret.Certificate.symbolCode b))
        (And
          (@LE.le.{0} Nat instLENat (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) a)
            (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) b))
          (@Eq.{1} Couret.Code30 (Couret.mul30 (Couret.Certificate.symbolCode a) (Couret.Certificate.symbolCode b))
            (Couret.Certificate.symbolCode r))))) := @_root_.Couret.Certificate.p2m_local_pairPresent_semantics

