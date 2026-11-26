-- Prove2me | Theorems.Thm_section5_discrete_momentum_evolution
-- name    : section5_discrete_momentum_evolution
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:06:40.527643+00:00
-- url     : https://prove2.me/theorems/ad8131d7-8008-548d-a814-f1a5b97f59d4
-- title:
--   Exact discrete momentum-square chirp circuit
-- statement:
--   Let q>0 and t be real. With centered discrete Fourier transform F_c, centered grid coordinate x_z=(U(z)−2^(q−1))√(4π/2^q), and D_t=diag(e^(itx_z²)), there is a one- and two-qubit gate circuit satisfying $$U_C=F_c^*D_tF_c,\qquad|C|\le3q^2+5q+3.$$ This is an exact discrete identity; no continuous oscillator approximation is asserted.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5OscillatorFactors.lean, lines 48–50. Uses the exact-QFT foundation by kmehltretter82, accepted Prove2Me submission 574f267d-70e8-417a-81da-58cae2f35605 (QAlgorithms.DeWolf.qft_circuit_exact), copied in Solutions/Section5QFTFoundation.lean.

import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5FourierCircuit
import Definitions.Def_Section5Verified_Section5OscillatorFactors
import Definitions.Def_Section5Verified_Section5QuadraticPhase
import Mathlib
import Theorems.Thm_section5_discrete_position_evolution
import Theorems.Thm_section5_elementary_centered_qft
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_discrete_momentum_evolution (q : ℕ) (hq : 0 < q) (t : ℝ) :
    ∃ c : Circuit gates12 q, c.size ≤ 3*q^2+5*q+3 ∧
      c.unitary=section5_momentum_chirp q t := by sorry
