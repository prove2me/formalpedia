-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_75
-- name    : Couret.Certificate.class_row_75
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:36:40.51602+00:00
-- url     : https://prove2.me/theorems/959ea8e3-6ca8-45e2-9f24-85135d2eb4ac
-- title:
--   Quotient certificate row 75
-- statement:
--   Consider the fixed eight-letter automaton with 147 table states and 101 quotient classes. For the fixed class $c=75$, all eight raw transition indices are below 101; its stored representative index is below 147 and maps back to $c$. For every other class $d$, the stored word $w_{c,d}$ distinguishes their future outputs, and every stored word has length at most two:
--
--   $$d\ne 75\ \Longrightarrow\ O(\delta^*(75,w_{75,d}))\ne O(\delta^*(d,w_{75,d})),\qquad |w_{75,d}|\le2.$$
--
--   This is one finite row of the quotient correctness and separation certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck10.lean, lines 12–12; source file SHA-256 4abd3edc4cf845a88970e6f34c3c70f0964d5bab12b37ee0a60dece7f4fa6c17; theorem Couret.Certificate.class_row_75

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_75 : ClassFacts 75 := by sorry



end Certificate
end Couret
