-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_80
-- name    : Couret.Certificate.class_row_80
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:36:45.398609+00:00
-- url     : https://prove2.me/theorems/b6c8ddc2-c82a-42ff-aeab-d62164cd87c5
-- title:
--   Quotient certificate row 80
-- statement:
--   Consider the fixed eight-letter automaton with 147 table states and 101 quotient classes. For the fixed class $c=80$, all eight raw transition indices are below 101; its stored representative index is below 147 and maps back to $c$. For every other class $d$, the stored word $w_{c,d}$ distinguishes their future outputs, and every stored word has length at most two:
--
--   $$d\ne 80\ \Longrightarrow\ O(\delta^*(80,w_{80,d}))\ne O(\delta^*(d,w_{80,d})),\qquad |w_{80,d}|\le2.$$
--
--   This is one finite row of the quotient correctness and separation certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck11.lean, lines 10–10; source file SHA-256 6ac91634408dd254d66afa048826d948860c35b84bbb1f35940f2d88f5f9b9b0; theorem Couret.Certificate.class_row_80

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_80 : ClassFacts 80 := by sorry





end Certificate
end Couret
