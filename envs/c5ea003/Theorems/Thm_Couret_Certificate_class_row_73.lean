-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_73
-- name    : Couret.Certificate.class_row_73
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:36:37.402337+00:00
-- url     : https://prove2.me/theorems/d526b349-211d-4489-babc-6644bb26570a
-- title:
--   Quotient certificate facts for class 73
-- statement:
--   For class $c=73$ in the specified 101-class quotient automaton over eight input symbols, all next-state indices are less than 101, its representative index is less than 147, and that representative belongs to class $c$. For each different class $d$, the prescribed separating word gives different final outputs when run from $c$ and $d$; for every class $d$, that word has length at most two.
--
--   $$0\le c=73<101.$$
--
--   This certifies one row of the explicit quotient and its distinguishing-word table.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck10.lean, lines 10–10; source file SHA-256 4abd3edc4cf845a88970e6f34c3c70f0964d5bab12b37ee0a60dece7f4fa6c17; theorem Couret.Certificate.class_row_73

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_73 : ClassFacts 73 := by sorry





end Certificate
end Couret
