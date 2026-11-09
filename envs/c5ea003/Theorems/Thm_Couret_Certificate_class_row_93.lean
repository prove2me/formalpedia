-- Prove2me | Theorems.Thm_Couret_Certificate_class_row_93
-- name    : Couret.Certificate.class_row_93
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:36:56.332145+00:00
-- url     : https://prove2.me/theorems/a1121b7b-502c-455f-a23b-960035b6d5ec
-- title:
--   Quotient certificate for class 93
-- statement:
--   For the fixed quotient class $c=93$ among the 101 classes, every one-symbol transition has index below 101; its designated representative has state index below 147 and belongs to class $c$. For every other class $d$, the supplied separating word produces different outputs when run from $c$ and $d$. For every class $d$, including $d=c$, that word has length at most two.
--
--   $$|w(c,d)|\le 2.$$
--
--   This finite certificate supplies representative validity and short distinguishing experiments for this particular quotient class.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ClassCheck13.lean, lines 9–9; source file SHA-256 0e56525f6a1f96b23830880695291a120e35838245ae02ee560f854cfb2ce130; theorem Couret.Certificate.class_row_93

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem class_row_93 : ClassFacts 93 := by sorry






end Certificate
end Couret
