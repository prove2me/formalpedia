-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_42
-- name    : Couret.Certificate.class_row_42
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:35:11.249331+00:00
-- url     : https://prove2.me/theorems/69f8e4ab-db4d-406f-a126-abb50f9b8d3c
-- title:
--   Quotient certificate row 42
-- statement:
--   Consider the fixed eight-letter automaton with 147 table states and 101 quotient classes. For the fixed class $c=42$, all eight raw transition indices are below 101; its stored representative index is below 147 and maps back to $c$. For every other class $d$, the stored word $w_{c,d}$ distinguishes their future outputs, and every stored word has length at most two:
--
--   $$d\ne 42\ \Longrightarrow\ O(\delta^*(42,w_{42,d}))\ne O(\delta^*(d,w_{42,d})),\qquad |w_{42,d}|\le2.$$
--
--   This is one finite row of the quotient correctness and separation certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck06.lean, lines 7–7; source file SHA-256 ec7a11c49ffffd30b5cbab5f16135184e9daa0e59404086172be1089cc24534d; theorem Couret.Certificate.class_row_42

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_42 : ClassFacts 42 := by sorry








end Certificate
end Couret
