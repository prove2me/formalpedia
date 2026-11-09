-- Prove2me | Definitions.Def_Couret_RankData_b110b8255ff4
-- name    : Couret_RankData_b110b8255ff4
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:30.836543+00:00
-- url     : https://prove2.me/theorems/bbb2a8dd-c23c-4cc4-873b-18fa983ceb37
-- title:
--   The 256-entry subproduct rank table
-- statement:
--   This contains the explicit array of 256 natural ranks assigned to all eight-bit unit-residue masks modulo 30. The rank function returns the stored array entry and uses zero as its default outside the array.
--
--   Separate finite row theorems certify the rank bounds, identity detection and transition growth needed in the length-threshold argument.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/RankData.lean; source file SHA-256 0f652bdd5b44fe9bcddd0c43a564e3b187787064220585aa93c6a15a8bd8926d

import Std
import Definitions.Def_Couret_SubproductSemantics_e0771d3a736f

namespace Couret.S5
def rankTable : Array Nat := #[0, 5, 1, 5, 1, 5, 1, 5, 1, 5, 1, 5, 1, 5, 1, 5, 1, 5, 1, 5, 1, 5, 2, 5, 1, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 3, 5, 2, 5, 3, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 3, 5, 2, 5, 3, 5, 1, 5, 1, 5, 1, 5, 2, 5, 1, 5, 2, 5, 2, 5, 2, 5, 1, 5, 2, 5, 1, 5, 2, 5, 2, 5, 2, 5, 2, 5, 3, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 3, 5, 2, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 1, 5, 1, 5, 1, 5, 1, 5, 1, 5, 1, 5, 1, 5, 1, 5, 1, 5, 2, 5, 1, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 3, 5, 3, 5, 2, 5, 3, 5, 3, 5, 3, 5, 2, 5, 2, 5, 3, 5, 3, 5, 2, 5, 3, 5, 3, 5, 3, 5, 1, 5, 2, 5, 1, 5, 2, 5, 2, 5, 2, 5, 2, 5, 2, 5, 1, 5, 2, 5, 1, 5, 2, 5, 2, 5, 3, 5, 2, 5, 3, 5, 2, 5, 2, 5, 3, 5, 3, 5, 2, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 3, 5, 4, 5]

def rank (m : Nat) : Nat := rankTable.getD m 0
end Couret.S5


