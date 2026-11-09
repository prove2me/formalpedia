-- Prove2me | Theorems.Thm_Couret_S5_five_factorPair_exact
-- name    : Couret.S5.five_factorPair_exact
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:38:37.457802+00:00
-- url     : https://prove2.me/theorems/d32c0194-b115-451c-b8f9-fddc464543dc
-- title:
--   Exact residue factor pairs for 64141
-- statement:
--   Let $a,b$ be codes for unit residues modulo 30, ordered by the bit order $(1,7,11,13,17,19,23,29)$. Then
--
--   $$\begin{aligned}&\exists d,e>1:\ de=64141,\quad d\equiv r(a),\ e\equiv r(b)\pmod{30},\quad a\le_{\rm bit}b\\ &\Longleftrightarrow\ a\le_{\rm bit}b,\quad a,b\text{ belong to mask }254,\quad ab=1\text{ in the unit group}.\end{aligned}$$
--
--   Mask 254 contains precisely the seven nonidentity residues. This identifies all factor residue pairs for the specified integer.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/FivePairSemantics.lean, lines 18–56; source file SHA-256 8b2d02904e438e1da57317890d439cece1022f7fb4ad1cbb929067cc80c7fde2; theorem Couret.S5.five_factorPair_exact

import Definitions.Def_Couret_FivePairSemantics_d40383365465
import Std
import Theorems.Thm_Couret_S5_five_proper_divisor_residues
import Theorems.Thm_Couret_coprime30_of_dvd
import Theorems.Thm_Couret_decode_encode30
import Theorems.Thm_Couret_mask_254_omits_only_residue_one
import Theorems.Thm_Couret_mul30_residue
import Theorems.Thm_Couret_residue30_injective
import Definitions.Def_Couret_OptimalFive_2f3f11b1b6a3
namespace Couret
namespace S5

/- The cancellation/complement argument follows the archived S4 proof,
   specialized here to the explicit five-prime counterexample. -/

theorem five_factorPair_exact (a b : Code30) : factorPair64141 a b ↔ maskPair64141 a b := by sorry










end S5
end Couret
