-- Prove2me | Theorems.Thm_Couret_maskSupport_zero
-- name    : Couret.maskSupport_zero
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:48:00.052783+00:00
-- url     : https://prove2.me/theorems/8f3b3ac0-b8f0-44b0-b565-4b42694e3e8a
-- title:
--   The zero mask has empty support
-- statement:
--   For every unit-residue code $u$ modulo 30,
--
--   $$u\notin\operatorname{support}(0).$$
--
--   Here support tests the corresponding one of the eight mask bits. This supplies the empty-mask base case.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/MaskSemantics.lean, lines 57–58; source file SHA-256 2b99a0c723013ccd7334d8463e5afb270be06050a7f31c47da8e9c55060a5eb7; import module renamed from MaskSemantics to BCS5MaskSemantics to disambiguate source modules; theorem Couret.maskSupport_zero

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret

theorem maskSupport_zero (u : Code30) : ¬ maskSupport 0 u := by sorry




























































end Couret
