-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_83
-- name    : Couret.Certificate.class_row_83
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:36:49.807131+00:00
-- url     : https://prove2.me/theorems/c42e0aeb-885a-48f0-a624-401f42a19f4c
-- title:
--   Quotient certificate row 83
-- statement:
--   Consider the fixed eight-letter automaton with 147 table states and 101 quotient classes. For the fixed class $c=83$, all eight raw transition indices are below 101; its stored representative index is below 147 and maps back to $c$. For every other class $d$, the stored word $w_{c,d}$ distinguishes their future outputs, and every stored word has length at most two:
--
--   $$d\ne 83\ \Longrightarrow\ O(\delta^*(83,w_{83,d}))\ne O(\delta^*(d,w_{83,d})),\qquad |w_{83,d}|\le2.$$
--
--   This is one finite row of the quotient correctness and separation certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck11.lean, lines 13–13; source file SHA-256 6ac91634408dd254d66afa048826d948860c35b84bbb1f35940f2d88f5f9b9b0; theorem Couret.Certificate.class_row_83

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_83 : ClassFacts 83 := by sorry


end Certificate
end Couret
