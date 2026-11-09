-- Prove2me | Theorems.Thm_Couret_decodeMaskState_injective
-- name    : Couret.decodeMaskState_injective
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:59:48.380385+00:00
-- url     : https://prove2.me/theorems/25db5b5f-03bd-4143-815c-d14617ec95bf
-- title:
--   Decoding is injective for canonical mask states
-- statement:
--   A modulo-30 mask state is either initial or an active pair $(r,m)$ consisting of a total residue code and a natural-number support mask. Call it canonical when active masks satisfy $m<256$; the initial state is canonical. If canonical states $s,t$ have identical decoded semantic states, then
--
--   $$s=t.$$
--
--   This certifies uniqueness of the bounded mask representation.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/MaskSemantics.lean, lines 191–208; source file SHA-256 2b99a0c723013ccd7334d8463e5afb270be06050a7f31c47da8e9c55060a5eb7; import module renamed from MaskSemantics to BCS5MaskSemantics to disambiguate source modules; theorem Couret.decodeMaskState_injective

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Theorems.Thm_Couret_canonical_mask_injective
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret

theorem decodeMaskState_injective (s t : MaskState) (hs : s.canonical)
    (ht : t.canonical) (he : decodeMaskState s = decodeMaskState t) : s = t := by sorry
























end Couret
