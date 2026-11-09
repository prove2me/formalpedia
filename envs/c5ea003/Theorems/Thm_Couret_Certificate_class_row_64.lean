-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_64
-- name    : Couret.Certificate.class_row_64
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:36:31.379915+00:00
-- url     : https://prove2.me/theorems/8101a6e2-2037-4835-bcf8-102c6c7c5d98
-- title:
--   Quotient certificate row 64
-- statement:
--   Consider the fixed eight-letter automaton with 147 table states and 101 quotient classes. For the fixed class $c=64$, all eight raw transition indices are below 101; its stored representative index is below 147 and maps back to $c$. For every other class $d$, the stored word $w_{c,d}$ distinguishes their future outputs, and every stored word has length at most two:
--
--   $$d\ne 64\ \Longrightarrow\ O(\delta^*(64,w_{64,d}))\ne O(\delta^*(d,w_{64,d})),\qquad |w_{64,d}|\le2.$$
--
--   This is one finite row of the quotient correctness and separation certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck09.lean, lines 8–8; source file SHA-256 93137fac5757cc8878f440938ce1dac00ff7ab7893f11178cea0b5ea08a1e1fe; theorem Couret.Certificate.class_row_64

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_64 : ClassFacts 64 := by sorry







end Certificate
end Couret
