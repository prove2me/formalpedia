-- Prove2me | Theorems.Thm_Couret_Certificate_quotientMachine_correct
-- name    : Couret.Certificate.quotientMachine_correct
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:25.825409+00:00
-- url     : https://prove2.me/theorems/492b308d-4b3f-4691-8d73-83749a47efeb
-- title:
--   Quotient machine preserves the table output
-- statement:
--   For every finite word $w$ over the eight-letter alphabet, the 101-class quotient machine and the 147-state table machine, each started at its initial state, have equal outputs:
--
--   $$O_Q(\operatorname{run}_Q(w))=O_T(\operatorname{run}_T(0,w)).$$
--
--   This validates quotient evaluation for arbitrary words, including the empty word.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/CertificateProofs.lean, lines 314–321; source file SHA-256 34105504de63d99f05e7d3427ba82853380bac1d8c053b618776cd7d98da83b2; theorem Couret.Certificate.quotientMachine_correct

import Definitions.Def_Couret_CertificateProofs_3244eb90a0e1
import Std
import Theorems.Thm_Couret_Certificate_quotient_congruence_checked
import Theorems.Thm_Couret_Certificate_quotient_initial
import Theorems.Thm_Couret_Certificate_quotient_output_checked
import Definitions.Def_Couret_CertificateData_653c7a96c17c

/-! Universal consequences of the finite certificate checks. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Couret
namespace Certificate

theorem quotientMachine_correct (w : Word Symbol) :
    quotientMachine.output (machineRun quotientMachine quotientMachine.initial w) =
      tableOutput (tableRun 0 w) := by sorry


end Certificate
end Couret
