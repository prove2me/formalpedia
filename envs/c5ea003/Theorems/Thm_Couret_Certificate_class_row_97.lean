-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_97
-- name    : Couret.Certificate.class_row_97
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:37:00.353715+00:00
-- url     : https://prove2.me/theorems/8a110588-749e-4d57-84f2-4c1fab338592
-- title:
--   Quotient certificate row 97
-- statement:
--   Consider the fixed eight-letter automaton with 147 table states and 101 quotient classes. For the fixed class $c=97$, all eight raw transition indices are below 101; its stored representative index is below 147 and maps back to $c$. For every other class $d$, the stored word $w_{c,d}$ distinguishes their future outputs, and every stored word has length at most two:
--
--   $$d\ne 97\ \Longrightarrow\ O(\delta^*(97,w_{97,d}))\ne O(\delta^*(d,w_{97,d})),\qquad |w_{97,d}|\le2.$$
--
--   This is one finite row of the quotient correctness and separation certificate.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck13.lean, lines 13–13; source file SHA-256 0e56525f6a1f96b23830880695291a120e35838245ae02ee560f854cfb2ce130; theorem Couret.Certificate.class_row_97

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_97 : ClassFacts 97 := by sorry


end Certificate
end Couret
