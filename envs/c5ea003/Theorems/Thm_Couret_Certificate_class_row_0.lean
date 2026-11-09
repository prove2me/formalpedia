-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_0
-- name    : Couret.Certificate.class_row_0
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:31:13.741601+00:00
-- url     : https://prove2.me/theorems/ba8cc584-f326-4fa4-a330-8c6b043aeac0
-- title:
--   Quotient certificate facts for class 0
-- statement:
--   For class $c=0$ in the specified 101-class quotient automaton over eight input symbols, all next-state indices are less than 101, its representative index is less than 147, and that representative belongs to class $c$. For each different class $d$, the prescribed separating word gives different final outputs when run from $c$ and $d$; for every class $d$, that word has length at most two.
--
--   $$0\le c=0<101.$$
--
--   This certifies one row of the explicit quotient and its distinguishing-word table.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck00.lean, lines 7–7; source file SHA-256 d5e13aa7f26bba3a1f164133d80624cf40118066a24bad710fc0e99d2e866f83; theorem Couret.Certificate.class_row_0

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_0 : ClassFacts 0 := by sorry








end Certificate
end Couret
