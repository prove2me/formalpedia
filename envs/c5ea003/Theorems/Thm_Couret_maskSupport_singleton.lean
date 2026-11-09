-- Prove2me | Theorems.Thm_Couret_maskSupport_singleton
-- name    : Couret.maskSupport_singleton
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:48:07.671629+00:00
-- url     : https://prove2.me/theorems/de364010-564c-4c2c-acce-b638bae5a117
-- title:
--   A singleton mask supports precisely its code
-- statement:
--   For unit residue codes $a,u$ modulo 30, $$u\in\operatorname{support}(\operatorname{singletonMask}(a))\iff u=a.$$
--
--   The mask uses the specified historical bit order.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/MaskSemantics.lean, lines 60–65; source file SHA-256 2b99a0c723013ccd7334d8463e5afb270be06050a7f31c47da8e9c55060a5eb7; import module renamed from MaskSemantics to BCS5MaskSemantics to disambiguate source modules; theorem Couret.maskSupport_singleton

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret

theorem maskSupport_singleton (a u : Code30) :
    maskSupport (singletonMask a) u ↔ u = a := by sorry


























































end Couret
