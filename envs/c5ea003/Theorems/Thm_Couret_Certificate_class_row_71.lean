-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_71
-- name    : Couret.Certificate.class_row_71
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:36:37.832003+00:00
-- url     : https://prove2.me/theorems/3dc73a37-bb65-42b4-a6d4-00e936309dd7
-- title:
--   Quotient certificate for class 71
-- statement:
--   For the fixed quotient class $c=71$ among the 101 classes, every one-symbol transition has index below 101; its designated representative has state index below 147 and belongs to class $c$. For every other class $d$, the supplied separating word produces different outputs when run from $c$ and $d$. For every class $d$, including $d=c$, that word has length at most two.
--
--   $$|w(c,d)|\le 2.$$
--
--   This finite certificate supplies representative validity and short distinguishing experiments for this particular quotient class.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck10.lean, lines 8–8; source file SHA-256 4abd3edc4cf845a88970e6f34c3c70f0964d5bab12b37ee0a60dece7f4fa6c17; theorem Couret.Certificate.class_row_71

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_71 : ClassFacts 71 := by sorry







end Certificate
end Couret
