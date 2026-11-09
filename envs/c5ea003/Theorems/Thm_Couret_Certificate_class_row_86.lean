-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_86
-- name    : Couret.Certificate.class_row_86
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:36:47.748556+00:00
-- url     : https://prove2.me/theorems/c0a8f213-f76a-4f65-8a49-64cf3111e6ba
-- title:
--   Quotient certificate row 86
-- statement:
--   Consider the fixed eight-letter automaton with 147 table states and 101 quotient classes. For the fixed class $c=86$, all eight raw transition indices are below 101; its stored representative index is below 147 and maps back to $c$. For every other class $d$, the stored word $w_{c,d}$ distinguishes their future outputs, and every stored word has length at most two:
--
--   $$d\ne 86\ \Longrightarrow\ O(\delta^*(86,w_{86,d}))\ne O(\delta^*(d,w_{86,d})),\qquad |w_{86,d}|\le2.$$
--
--   This is one finite row of the quotient correctness and separation certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck12.lean, lines 9–9; source file SHA-256 5d80c423cc8259445e6fcc2a45443cf39d99bcccd210999137982b5d10b195aa; theorem Couret.Certificate.class_row_86

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_86 : ClassFacts 86 := by sorry






end Certificate
end Couret
