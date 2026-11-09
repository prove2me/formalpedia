-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_37
-- name    : Couret.Certificate.class_row_37
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:35:09.080648+00:00
-- url     : https://prove2.me/theorems/7d1356cf-220d-4b7b-891a-76b74b1ced44
-- title:
--   Quotient certificate row 37
-- statement:
--   Consider the fixed eight-letter automaton with 147 table states and 101 quotient classes. For the fixed class $c=37$, all eight raw transition indices are below 101; its stored representative index is below 147 and maps back to $c$. For every other class $d$, the stored word $w_{c,d}$ distinguishes their future outputs, and every stored word has length at most two:
--
--   $$d\ne 37\ \Longrightarrow\ O(\delta^*(37,w_{37,d}))\ne O(\delta^*(d,w_{37,d})),\qquad |w_{37,d}|\le2.$$
--
--   This is one finite row of the quotient correctness and separation certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck05.lean, lines 9–9; source file SHA-256 a0be6a9afb4bdcff73d3db25c04929b874085b1d09d3856f7e974272a249a229; theorem Couret.Certificate.class_row_37

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_37 : ClassFacts 37 := by sorry






end Certificate
end Couret
