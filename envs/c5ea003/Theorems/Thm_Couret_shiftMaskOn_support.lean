-- Prove2me | Theorems.Thm_Couret_shiftMaskOn_support
-- name    : Couret.shiftMaskOn_support
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:54.344613+00:00
-- url     : https://prove2.me/theorems/29c48c92-1944-4b20-93a4-f60fda89ed7d
-- title:
--   Support of a restricted mask shift
-- statement:
--   Let $g,u$ be unit-residue codes modulo 30, $m\in\mathbb N$ a mask, and $L$ any finite list of codes. The restricted shift scans $L$ and inserts $gv$ for each $v$ whose bit is present in $m$. Then
--
--   $$u\in\operatorname{support}(\operatorname{shiftOn}(g,m,L))\Longleftrightarrow\exists v\in L:\ v\in\operatorname{support}(m),\ gv=u.$$
--
--   The list may be empty or contain duplicates; no canonical-mask premise is required.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/MaskSemantics.lean, lines 113–139; source file SHA-256 2b99a0c723013ccd7334d8463e5afb270be06050a7f31c47da8e9c55060a5eb7; import module renamed from MaskSemantics to BCS5MaskSemantics to disambiguate source modules; theorem Couret.shiftMaskOn_support

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Theorems.Thm_Couret_maskSupport_or
import Theorems.Thm_Couret_maskSupport_singleton
import Theorems.Thm_Couret_maskSupport_zero
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret

theorem shiftMaskOn_support (g : Code30) (mask : Nat) (letters : List Code30)
    (u : Code30) :
    maskSupport (shiftMaskOn g mask letters) u ↔
      ∃ v, v ∈ letters ∧ maskSupport mask v ∧ mul30 g v = u := by sorry












































end Couret
