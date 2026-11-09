-- Prove2me | Theorems.Thm_Couret_Certificate_decode_injective
-- name    : Couret.Certificate.decode_injective
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:36:59.36403+00:00
-- url     : https://prove2.me/theorems/c7c8acd0-1280-4b09-a637-e0e0b5ee8f6f
-- title:
--   The eight-bit state encoding is injective
-- statement:
--   Let $a,b$ be optional pairs consisting of an eight-symbol residue code and an eight-bit mask. Decode the absent pair as the initial state and a present pair as its total residue and represented support. Then
--
--   $$\operatorname{decode}(a)=\operatorname{decode}(b)\Longrightarrow a=b.$$
--
--   This ensures the finite encoding faithfully represents semantic states.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/MaskSemantics.lean, lines 98–109; source file SHA-256 e62d6e7eba64af2437560f86dbb440160326ed6ca55e9e3151a62894e53af0c5; import module renamed from MaskSemantics to BCS4MaskSemantics to disambiguate source modules; theorem Couret.Certificate.decode_injective

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

theorem decode_injective {a b : EncodedState} (h : decode a = decode b) : a = b := by sorry
















end Certificate
end Couret
