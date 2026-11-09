-- Prove2me | Theorems.Thm_Couret_Certificate_pairPresent_semantics
-- name    : Couret.Certificate.pairPresent_semantics
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:37:29.544355+00:00
-- url     : https://prove2.me/theorems/c3660fd6-e259-4b1f-b260-73e453648b97
-- title:
--   Meaning of an encoded factor pair
-- statement:
--   For alphabet symbols $r,a,b$ and an eight-bit mask $m$, the pair-presence Boolean on active encoding $(r,m)$ is true exactly when both residue codes of $a,b$ lie in the mask support, their symbol indices satisfy $a\le b$, and their product modulo 30 is the code of $r$. $$\operatorname{pairPresent}((r,m),a,b)=\mathrm{true}\iff a,b\text{ are supported},\ a\le b,\ ab=r.$$
--
--   The index order prevents double counting unordered pairs.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/MaskSemantics.lean, lines 133–137; source file SHA-256 e62d6e7eba64af2437560f86dbb440160326ed6ca55e9e3151a62894e53af0c5; import module renamed from MaskSemantics to BCS4MaskSemantics to disambiguate source modules; theorem Couret.Certificate.pairPresent_semantics

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

theorem pairPresent_semantics (r : Symbol) (m : Mask) (a b : Symbol) :
    pairPresent (some (r,m)) a b = true ↔
      maskSupport m (symbolCode a) ∧ maskSupport m (symbolCode b) ∧
      a.val ≤ b.val ∧ mul30 (symbolCode a) (symbolCode b) = symbolCode r := by sorry








end Certificate
end Couret
