-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_29
-- name    : Couret.Certificate.class_row_29
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:34:53.398382+00:00
-- url     : https://prove2.me/theorems/61389841-4500-4e04-afe8-492b8f59615f
-- title:
--   Quotient certificate row 29
-- statement:
--   Consider the fixed eight-letter automaton with 147 table states and 101 quotient classes. For the fixed class $c=29$, all eight raw transition indices are below 101; its stored representative index is below 147 and maps back to $c$. For every other class $d$, the stored word $w_{c,d}$ distinguishes their future outputs, and every stored word has length at most two:
--
--   $$d\ne 29\ \Longrightarrow\ O(\delta^*(29,w_{29,d}))\ne O(\delta^*(d,w_{29,d})),\qquad |w_{29,d}|\le2.$$
--
--   This is one finite row of the quotient correctness and separation certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck04.lean, lines 8–8; source file SHA-256 1dab3a04e3e5265cdb839d6e630aded857a5fd7ec970b07cc510fbed204924b9; theorem Couret.Certificate.class_row_29

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_29 : ClassFacts 29 := by sorry







end Certificate
end Couret
