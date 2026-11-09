-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_10
-- name    : Couret.Certificate.class_row_10
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:31:21.66899+00:00
-- url     : https://prove2.me/theorems/64054920-09a2-4476-b798-ebfa7e827c71
-- title:
--   Quotient certificate row 10
-- statement:
--   Consider the fixed eight-letter automaton with 147 table states and 101 quotient classes. For the fixed class $c=10$, all eight raw transition indices are below 101; its stored representative index is below 147 and maps back to $c$. For every other class $d$, the stored word $w_{c,d}$ distinguishes their future outputs, and every stored word has length at most two:
--
--   $$d\ne 10\ \Longrightarrow\ O(\delta^*(10,w_{10,d}))\ne O(\delta^*(d,w_{10,d})),\qquad |w_{10,d}|\le2.$$
--
--   This is one finite row of the quotient correctness and separation certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck01.lean, lines 10–10; source file SHA-256 e18436e83333c440ba569a448ec44f2aef18f3b5ab1ed17a044031a07cb1ec92; theorem Couret.Certificate.class_row_10

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_10 : ClassFacts 10 := by sorry





end Certificate
end Couret
