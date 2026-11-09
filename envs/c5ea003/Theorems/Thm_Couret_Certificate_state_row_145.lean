-- Prove2me | Theorems.Thm_Couret_Certificate_state_row_145
-- name    : Couret.Certificate.state_row_145
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:22:12.464032+00:00
-- url     : https://prove2.me/theorems/0f7ddd66-81d4-4038-9521-3154aedbad6f
-- title:
--   Finite automaton certificate for state 145
-- statement:
--   For the fixed state index $i=145$ in the 147-state certificate, every symbol transition has index below 147, and its class index is below 101. Locating the stored encoding returns $i$, and the encoding is absent exactly when $i=0$. Every stored transition satisfies the encoded semantic transition rule. Running the supplied reachability word from state zero reaches $i$; this word is nonempty if $i\ne0$. The stored output equals both the encoding output mask and its presence count. Classification commutes with each symbol transition, and the stored output equals the quotient output of the state class.
--
--   $$\operatorname{run}(0,w_i)=i.$$
--
--   This bundles all table and semantic consistency checks needed for this single finite state.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/StateCheck20.lean, lines 12–12; source file SHA-256 0c6f828e0acba243c758092db9373fc7006f0b2f6f4de944b336fecd960055f1; theorem Couret.Certificate.state_row_145

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem state_row_145 : StateFacts 145 := by sorry



end Certificate
end Couret
