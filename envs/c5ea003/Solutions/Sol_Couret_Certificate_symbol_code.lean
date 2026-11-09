-- Prove2me | solution 1 for Couret.Certificate.symbol_code
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:37:12.959399+00:00
-- url     : https://prove2.me/submissions/6717f1de-46d2-43d8-93c9-d730d06892db

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
















theorem p2m_local_symbol_code : ∀ g : Code30, symbolCode (codeSymbol g) = g := by decide

































end Certificate
end Couret

theorem solution : ∀ (g : Couret.Code30), @Eq.{1} Couret.Code30 (Couret.Certificate.symbolCode (Couret.Certificate.codeSymbol g)) g := @_root_.Couret.Certificate.p2m_local_symbol_code

