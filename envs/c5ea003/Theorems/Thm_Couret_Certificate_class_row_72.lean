-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_72
-- name    : Couret.Certificate.class_row_72
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:36:36.351189+00:00
-- url     : https://prove2.me/theorems/43fd6f40-e12c-445a-8ef9-81c149d8c32d
-- title:
--   Quotient certificate row 72
-- statement:
--   Consider the fixed eight-letter automaton with 147 table states and 101 quotient classes. For the fixed class $c=72$, all eight raw transition indices are below 101; its stored representative index is below 147 and maps back to $c$. For every other class $d$, the stored word $w_{c,d}$ distinguishes their future outputs, and every stored word has length at most two:
--
--   $$d\ne 72\ \Longrightarrow\ O(\delta^*(72,w_{72,d}))\ne O(\delta^*(d,w_{72,d})),\qquad |w_{72,d}|\le2.$$
--
--   This is one finite row of the quotient correctness and separation certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck10.lean, lines 9–9; source file SHA-256 4abd3edc4cf845a88970e6f34c3c70f0964d5bab12b37ee0a60dece7f4fa6c17; theorem Couret.Certificate.class_row_72

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_72 : ClassFacts 72 := by sorry






end Certificate
end Couret
