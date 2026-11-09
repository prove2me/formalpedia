-- Prove2me | Theorems.Thm_Couret_Certificate_state_row_129
-- name    : Couret.Certificate.state_row_129
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:20:56.994116+00:00
-- url     : https://prove2.me/theorems/b05bc2c5-b2f0-42c4-97e7-fb9cba34ed5a
-- title:
--   Finite automaton certificate for state 129
-- statement:
--   For the fixed state index $i=129$ in the 147-state certificate, every symbol transition has index below 147, and its class index is below 101. Locating the stored encoding returns $i$, and the encoding is absent exactly when $i=0$. Every stored transition satisfies the encoded semantic transition rule. Running the supplied reachability word from state zero reaches $i$; this word is nonempty if $i\ne0$. The stored output equals both the encoding output mask and its presence count. Classification commutes with each symbol transition, and the stored output equals the quotient output of the state class.
--
--   $$\operatorname{run}(0,w_i)=i.$$
--
--   This bundles all table and semantic consistency checks needed for this single finite state.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/StateCheck18.lean, lines 10–10; source file SHA-256 79703b4f17b61577c210152d80de42fd64768a3bc5d50e939b1514c7f1f1d094; theorem Couret.Certificate.state_row_129

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem state_row_129 : StateFacts 129 := by sorry





end Certificate
end Couret
