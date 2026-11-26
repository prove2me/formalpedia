-- Prove2me | Theorems.Thm_section5_oscillator_factor_circuit
-- name    : section5_oscillator_factor_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:09:45.784691+00:00
-- url     : https://prove2.me/theorems/6ab483c4-b143-4d65-9595-83ebe5bcd1e1
-- title:
--   Exact circuit for a product of oscillator chirps
-- statement:
--   Let q>0 and a,b be real. Put D_t=diag(e^(itx_z²)) on the centered q-bit grid, F_c the centered Fourier transform and P_t=F_c^*D_tF_c. The product P_a D_b P_a has an exact one- and two-qubit implementation with $$U_C=P_aD_bP_a,\qquad|C|\le7q^2+11q+7.$$ The assertion concerns this discrete product, conditional on no continuous approximation claim.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5OscillatorFactors.lean, lines 67–69. Uses the exact-QFT foundation by kmehltretter82, accepted Prove2Me submission 574f267d-70e8-417a-81da-58cae2f35605 (QAlgorithms.DeWolf.qft_circuit_exact), copied in Solutions/Section5QFTFoundation.lean.

import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5OscillatorFactors
import Definitions.Def_Section5Verified_Section5QuadraticPhase
import Mathlib
import Theorems.Thm_section5_discrete_momentum_evolution
import Theorems.Thm_section5_discrete_position_evolution
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_oscillator_factor_circuit (q : ℕ) (hq : 0 < q) (a b : ℝ) :
    ∃ c : Circuit gates12 q, c.size ≤ 7*q^2+11*q+7 ∧
      c.unitary=section5_oscillator_chirps q a b := by sorry
