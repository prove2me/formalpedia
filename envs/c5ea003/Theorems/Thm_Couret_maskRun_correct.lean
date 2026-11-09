-- Prove2me | Theorems.Thm_Couret_maskRun_correct
-- name    : Couret.maskRun_correct
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:45.644409+00:00
-- url     : https://prove2.me/theorems/e947bc72-ca87-496b-9a4f-13c78cc3248c
-- title:
--   The bit-mask run computes the semantic state
-- statement:
--   For every word $w$ in the eight unit residues modulo 30,
--
--   $$\operatorname{decode}(\operatorname{maskRun}(w))=\operatorname{semanticState}(w).$$
--
--   The empty word yields the initial state. For a nonempty word the semantic state consists of its total product and the products of nonempty proper selections of labeled occurrences. This validates the mask implementation.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/MaskSemantics.lean, lines 239–241; source file SHA-256 2b99a0c723013ccd7334d8463e5afb270be06050a7f31c47da8e9c55060a5eb7; import module renamed from MaskSemantics to BCS5MaskSemantics to disambiguate source modules; theorem Couret.maskRun_correct

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Theorems.Thm_Couret_maskSupport_or
import Theorems.Thm_Couret_maskSupport_singleton
import Theorems.Thm_Couret_maskSupport_zero
import Theorems.Thm_Couret_run_correct
import Theorems.Thm_Couret_shiftMask_support
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret

theorem maskRun_correct (w : Word Code30) :
    decodeMaskState (maskRun w) = semanticState mod30Product w := by sorry














end Couret
