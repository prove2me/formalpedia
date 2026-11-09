-- Prove2me | Theorems.Thm_Couret_Certificate_StepValid_sound
-- name    : Couret.Certificate.StepValid_sound
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:31:17.221491+00:00
-- url     : https://prove2.me/theorems/f2b97ad9-1a5e-43f2-97b4-34d32b60496e
-- title:
--   Encoded transitions agree with semantic transitions
-- statement:
--   Let $s,t$ be encoded states and $g$ an alphabet symbol. If the finite transition certificate declares this step valid, then $$\operatorname{decode}(t)=\operatorname{step}(\operatorname{decode}(s),\operatorname{code}(g)),$$ where the semantic step uses multiplication of unit residues modulo 30. This converts encoded validity into the semantic state equation.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/MaskSemantics.lean, lines 170–190; source file SHA-256 e62d6e7eba64af2437560f86dbb440160326ed6ca55e9e3151a62894e53af0c5; import module renamed from MaskSemantics to BCS4MaskSemantics to disambiguate source modules; theorem Couret.Certificate.StepValid_sound

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

theorem StepValid_sound {s t : EncodedState} {g : Symbol} (h : StepValid s t g) :
    decode t = step mod30Product (decode s) (symbolCode g) := by sorry


end Certificate
end Couret
