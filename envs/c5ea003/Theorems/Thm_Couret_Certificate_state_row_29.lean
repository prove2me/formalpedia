-- Prove2me | Theorems.Thm_Couret_Certificate_state_row_29
-- name    : Couret.Certificate.state_row_29
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:22:33.417614+00:00
-- url     : https://prove2.me/theorems/44fa9be7-eb89-4216-92e0-03c75d8407a4
-- title:
--   Finite-state certificate facts for state 29
-- statement:
--   For state $i=29$ of the specified 147-state automaton over eight symbols: every transition index is less than 147; its quotient-class index is less than 101; locating its encoded entry returns $i$; the entry is empty exactly when $i=0$; every symbol transition satisfies the encoded semantic step relation; and running its prescribed reachability word from state zero reaches $i$. That word is nonempty if $i\ne0$. The tabulated output equals both the output-mask observation and the presence count. For every symbol, taking its transition and then its quotient class equals taking the quotient transition, and the state output equals its class output.
--
--   $$0\le i=29<147.$$
--
--   This certifies a single explicit automaton row, including its reachability and semantic consistency.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/StateCheck04.lean, lines 8–8; source file SHA-256 c395dfb84c1344beeea709e6e62f144079a54fae2bdb56d6d1c896263f809fcb; theorem Couret.Certificate.state_row_29

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem state_row_29 : StateFacts 29 := by sorry







end Certificate
end Couret
