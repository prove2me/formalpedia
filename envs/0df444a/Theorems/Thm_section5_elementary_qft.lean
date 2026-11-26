-- Prove2me | Theorems.Thm_section5_elementary_qft
-- name    : section5_elementary_qft
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:46:39.2227+00:00
-- url     : https://prove2.me/theorems/b65ad55a-b571-5ec6-bdb9-bb389dfb563e
-- title:
--   Exact elementary-gate quantum Fourier transform
-- statement:
--   For every q≥0 there exists a circuit C of arbitrary one- and two-qubit gates on q wires implementing the standard q-qubit quantum Fourier transform exactly: $$U_C=F_{2^q},\qquad|C|\le q^2.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5FourierCircuit.lean, lines 48–49. Uses the exact-QFT foundation by kmehltretter82, accepted Prove2Me submission 574f267d-70e8-417a-81da-58cae2f35605 (QAlgorithms.DeWolf.qft_circuit_exact), copied in Solutions/Section5QFTFoundation.lean.

import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5FourierCircuit
import Definitions.Def_Section5Verified_Section5QFTFoundation
import Definitions.Def_Section5Verified_Section5QuadraticPhase
import Mathlib
import Theorems.Thm_SolQFTCircuitExact_embedOp_diagonal
import Theorems.Thm_SolQFTCircuitExact_qftQubits_step
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_elementary_qft (q : ℕ) :
    ∃ c : Circuit gates12 q, c.size ≤ q^2 ∧ c.unitary=qftQubits q := by sorry
