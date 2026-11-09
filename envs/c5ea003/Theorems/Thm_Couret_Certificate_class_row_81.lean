-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_81
-- name    : Couret.Certificate.class_row_81
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:36:45.184384+00:00
-- url     : https://prove2.me/theorems/76dfa532-b18f-4590-a659-fadc70d9f450
-- title:
--   Quotient certificate facts for class 81
-- statement:
--   For class $c=81$ in the specified 101-class quotient automaton over eight input symbols, all next-state indices are less than 101, its representative index is less than 147, and that representative belongs to class $c$. For each different class $d$, the prescribed separating word gives different final outputs when run from $c$ and $d$; for every class $d$, that word has length at most two.
--
--   $$0\le c=81<101.$$
--
--   This certifies one row of the explicit quotient and its distinguishing-word table.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck11.lean, lines 11–11; source file SHA-256 6ac91634408dd254d66afa048826d948860c35b84bbb1f35940f2d88f5f9b9b0; theorem Couret.Certificate.class_row_81

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_81 : ClassFacts 81 := by sorry




end Certificate
end Couret
