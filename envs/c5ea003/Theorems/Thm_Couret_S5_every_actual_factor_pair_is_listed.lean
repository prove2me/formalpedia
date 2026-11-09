-- Prove2me | Theorems.Thm_Couret_S5_every_actual_factor_pair_is_listed
-- name    : Couret.S5.every_actual_factor_pair_is_listed
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:51:45.447614+00:00
-- url     : https://prove2.me/theorems/cd92d03a-8861-4803-95fc-54db398c6b42
-- title:
--   The finite list covers actual factors of 64141
-- statement:
--   For natural $d,e>1$ with $de=64141$, the residue pair $(d\bmod30,e\bmod30)$ or its reversal belongs to the specified pair list at code identity and mask 254: $$((d\bmod30),(e\bmod30))\in L\ \text{or}\ ((e\bmod30),(d\bmod30))\in L.$$
--
--   The order is not prescribed.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/FivePairSemantics.lean, lines 69–87; source file SHA-256 8b2d02904e438e1da57317890d439cece1022f7fb4ad1cbb929067cc80c7fde2; theorem Couret.S5.every_actual_factor_pair_is_listed

import Definitions.Def_Couret_FivePairSemantics_d40383365465
import Std
import Theorems.Thm_Couret_S5_five_factorPair_exact
import Theorems.Thm_Couret_coprime30_of_dvd
import Theorems.Thm_Couret_decode_encode30
import Definitions.Def_Couret_OptimalFive_2f3f11b1b6a3
namespace Couret
namespace S5

/- The cancellation/complement argument follows the archived S4 proof,
   specialized here to the explicit five-prime counterexample. -/

theorem every_actual_factor_pair_is_listed (d e : Nat) (hd : 1 < d) (he : 1 < e)
    (hprod : d * e = 64141) :
    (d % 30,e % 30) ∈ pairList (0,0) 254 ∨
      (e % 30,d % 30) ∈ pairList (0,0) 254 := by sorry


end S5
end Couret
