-- Prove2me | Theorems.Thm_Couret_maskSupport_or
-- name    : Couret.maskSupport_or
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:47:49.249595+00:00
-- url     : https://prove2.me/theorems/2cb8c8ac-7e46-4fc4-9820-6c043d5eb337
-- title:
--   Bitwise union represents union of residue supports
-- statement:
--   Write $C=\mathbb Z/2\mathbb Z\times\mathbb Z/4\mathbb Z$, with residue map $\rho$ taking $(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)$ to $1,7,19,13,11,17,29,23$, respectively. For arbitrary natural masks $a,b$ and $u\in C$,
--
--   $$u\in\operatorname{supp}(a\mathbin{\mathrm{OR}}b)\iff u\in\operatorname{supp}(a)\ \lor\ u\in\operatorname{supp}(b).$$
--
--   No eight-bit bound is needed for this support identity.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/MaskSemantics.lean, lines 67–69; source file SHA-256 2b99a0c723013ccd7334d8463e5afb270be06050a7f31c47da8e9c55060a5eb7; import module renamed from MaskSemantics to BCS5MaskSemantics to disambiguate source modules; theorem Couret.maskSupport_or

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret

theorem maskSupport_or (a b : Nat) (u : Code30) :
    maskSupport (a ||| b) u ↔ maskSupport a u ∨ maskSupport b u := by sorry
























































end Couret
