-- Prove2me | Theorems.Thm_Couret_mask_254_omits_only_residue_one
-- name    : Couret.mask_254_omits_only_residue_one
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:57.281197+00:00
-- url     : https://prove2.me/theorems/6634c5f3-889c-4935-868e-5ae3121b45da
-- title:
--   Mask 254 represents every unit residue except one
-- statement:
--   Write $C=\mathbb Z/2\mathbb Z\times\mathbb Z/4\mathbb Z$, with residue map $\rho$ taking $(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)$ to $1,7,19,13,11,17,29,23$, respectively. For every $u\in C$,
--
--   $$u\in\operatorname{supp}(254)\iff\rho(u)\ne1.$$
--
--   This records the interpretation of the concrete eight-bit mask $11111110_2$.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/MaskSemantics.lean, lines 254–255; source file SHA-256 2b99a0c723013ccd7334d8463e5afb270be06050a7f31c47da8e9c55060a5eb7; import module renamed from MaskSemantics to BCS5MaskSemantics to disambiguate source modules; theorem Couret.mask_254_omits_only_residue_one

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret

theorem mask_254_omits_only_residue_one : ∀ u : Code30,
    maskSupport 254 u ↔ residue30 u ≠ 1 := by sorry






end Couret
