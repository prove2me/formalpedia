-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_47
-- name    : Couret.Certificate.class_row_47
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:35:12.57619+00:00
-- url     : https://prove2.me/theorems/ef9afabc-e825-4a4a-a98c-4c401b6548dc
-- title:
--   Quotient certificate for class 47
-- statement:
--   For the fixed quotient class $c=47$ among the 101 classes, every one-symbol transition has index below 101; its designated representative has state index below 147 and belongs to class $c$. For every other class $d$, the supplied separating word produces different outputs when run from $c$ and $d$. For every class $d$, including $d=c$, that word has length at most two.
--
--   $$|w(c,d)|\le 2.$$
--
--   This finite certificate supplies representative validity and short distinguishing experiments for this particular quotient class.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck06.lean, lines 12–12; source file SHA-256 ec7a11c49ffffd30b5cbab5f16135184e9daa0e59404086172be1089cc24534d; theorem Couret.Certificate.class_row_47

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_47 : ClassFacts 47 := by sorry



end Certificate
end Couret
