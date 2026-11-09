-- Prove2me | Theorems.Thm_Couret_shiftMaskOn_lt_256
-- name    : Couret.shiftMaskOn_lt_256
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:00.67744+00:00
-- url     : https://prove2.me/theorems/5285e918-2f51-45b3-8e96-ef957e3dacc8
-- title:
--   Partial mask shifting stays within eight bits
-- statement:
--   For every residue code $g$, natural mask $m$, and finite list $L$ of residue codes, $$\operatorname{shiftMaskOn}(g,m,L)<256.$$ Neither the input mask nor the list is required canonical; repeated list entries are allowed.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/MaskSemantics.lean, lines 100–111; source file SHA-256 2b99a0c723013ccd7334d8463e5afb270be06050a7f31c47da8e9c55060a5eb7; import module renamed from MaskSemantics to BCS5MaskSemantics to disambiguate source modules; theorem Couret.shiftMaskOn_lt_256

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Theorems.Thm_Couret_singletonMask_lt_256
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret

theorem shiftMaskOn_lt_256 (g : Code30) (mask : Nat) (letters : List Code30) :
    shiftMaskOn g mask letters < 256 := by sorry














































end Couret
