-- Prove2me | Theorems.Thm_Couret_Certificate_state_row_15
-- name    : Couret.Certificate.state_row_15
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:22:13.41037+00:00
-- url     : https://prove2.me/theorems/eb678fd4-eb69-49e5-b7cf-4996d0549041
-- title:
--   Finite-state certificate facts for state 15
-- statement:
--   For state $i=15$ of the specified 147-state automaton over eight symbols: every transition index is less than 147; its quotient-class index is less than 101; locating its encoded entry returns $i$; the entry is empty exactly when $i=0$; every symbol transition satisfies the encoded semantic step relation; and running its prescribed reachability word from state zero reaches $i$. That word is nonempty if $i\ne0$. The tabulated output equals both the output-mask observation and the presence count. For every symbol, taking its transition and then its quotient class equals taking the quotient transition, and the state output equals its class output.
--
--   $$0\le i=15<147.$$
--
--   This certifies a single explicit automaton row, including its reachability and semantic consistency.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/StateCheck02.lean, lines 8–8; source file SHA-256 1f3e3a21c0fb577b66ccbcbb55e731b433bff5f6592f950bdf062347d5def35f; theorem Couret.Certificate.state_row_15

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem state_row_15 : StateFacts 15 := by sorry







end Certificate
end Couret
