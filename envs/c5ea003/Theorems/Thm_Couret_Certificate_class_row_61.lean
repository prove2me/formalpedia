-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_61
-- name    : Couret.Certificate.class_row_61
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:36:26.3092+00:00
-- url     : https://prove2.me/theorems/cf0fbe15-b4b5-415d-a340-966ed755366b
-- title:
--   Quotient certificate row 61
-- statement:
--   Consider the fixed eight-letter automaton with 147 table states and 101 quotient classes. For the fixed class $c=61$, all eight raw transition indices are below 101; its stored representative index is below 147 and maps back to $c$. For every other class $d$, the stored word $w_{c,d}$ distinguishes their future outputs, and every stored word has length at most two:
--
--   $$d\ne 61\ \Longrightarrow\ O(\delta^*(61,w_{61,d}))\ne O(\delta^*(d,w_{61,d})),\qquad |w_{61,d}|\le2.$$
--
--   This is one finite row of the quotient correctness and separation certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck08.lean, lines 12–12; source file SHA-256 43975a315ea9ae509627f12119e0c20170de72e93bcf6b24d49a5dd35a0f1424; theorem Couret.Certificate.class_row_61

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_61 : ClassFacts 61 := by sorry



end Certificate
end Couret
