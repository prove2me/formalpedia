-- Prove2me | Theorems.Thm_Couret_Certificate_state_row_1
-- name    : Couret.Certificate.state_row_1
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:20:28.445359+00:00
-- url     : https://prove2.me/theorems/6cee1fa7-e855-476e-a389-e9079c5b7ac3
-- title:
--   Finite automaton certificate for state 1
-- statement:
--   For the fixed state index $i=1$ in the 147-state certificate, every symbol transition has index below 147, and its class index is below 101. Locating the stored encoding returns $i$, and the encoding is absent exactly when $i=0$. Every stored transition satisfies the encoded semantic transition rule. Running the supplied reachability word from state zero reaches $i$; this word is nonempty if $i\ne0$. The stored output equals both the encoding output mask and its presence count. Classification commutes with each symbol transition, and the stored output equals the quotient output of the state class.
--
--   $$\operatorname{run}(0,w_i)=i.$$
--
--   This bundles all table and semantic consistency checks needed for this single finite state.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/StateCheck00.lean, lines 8–8; source file SHA-256 575115fb5e0e55adce097f37a187de18860d6ad3f18ba0aa137b31f768ef4558; theorem Couret.Certificate.state_row_1

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem state_row_1 : StateFacts 1 := by sorry







end Certificate
end Couret
