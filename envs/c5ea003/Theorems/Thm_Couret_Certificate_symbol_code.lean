-- Prove2me | Theorems.Thm_Couret_Certificate_symbol_code
-- name    : Couret.Certificate.symbol_code
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:37:08.940478+00:00
-- url     : https://prove2.me/theorems/2c045c4d-77fa-4b3e-bc46-213b3e802685
-- title:
--   Residue encoding and symbol decoding compose to the identity
-- statement:
--   Write $C=\mathbb Z/2\mathbb Z\times\mathbb Z/4\mathbb Z$, with residue map $\rho$ taking $(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)$ to $1,7,19,13,11,17,29,23$, respectively. If $s:C\to\{0,\ldots,7\}$ is the symbol encoder and $c$ the symbol-to-code map in the specified residue ordering, then
--
--   $$c(s(g))=g\qquad(g\in C).$$
--
--   This fixes one direction of the equivalence between residue coordinates and eight symbols.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/MaskSemantics.lean, lines 58–58; source file SHA-256 e62d6e7eba64af2437560f86dbb440160326ed6ca55e9e3151a62894e53af0c5; import module renamed from MaskSemantics to BCS4MaskSemantics to disambiguate source modules; theorem Couret.Certificate.symbol_code

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

theorem symbol_code : ∀ g : Code30, symbolCode (codeSymbol g) = g := by sorry


































end Certificate
end Couret
