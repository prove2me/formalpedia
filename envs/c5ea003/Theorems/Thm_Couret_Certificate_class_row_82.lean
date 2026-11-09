-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_82
-- name    : Couret.Certificate.class_row_82
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:36:48.343385+00:00
-- url     : https://prove2.me/theorems/84ea7e5e-7f77-4f90-81f4-e43ffce6fa1b
-- title:
--   Quotient certificate for class 82
-- statement:
--   For the fixed quotient class $c=82$ among the 101 classes, every one-symbol transition has index below 101; its designated representative has state index below 147 and belongs to class $c$. For every other class $d$, the supplied separating word produces different outputs when run from $c$ and $d$. For every class $d$, including $d=c$, that word has length at most two.
--
--   $$|w(c,d)|\le 2.$$
--
--   This finite certificate supplies representative validity and short distinguishing experiments for this particular quotient class.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck11.lean, lines 12–12; source file SHA-256 6ac91634408dd254d66afa048826d948860c35b84bbb1f35940f2d88f5f9b9b0; theorem Couret.Certificate.class_row_82

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_82 : ClassFacts 82 := by sorry



end Certificate
end Couret
