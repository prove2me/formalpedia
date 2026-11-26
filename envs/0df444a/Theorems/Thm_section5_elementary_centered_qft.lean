-- Prove2me | Theorems.Thm_section5_elementary_centered_qft
-- name    : section5_elementary_centered_qft
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:00:56.922735+00:00
-- url     : https://prove2.me/theorems/6b7f31c5-65f2-5608-b32b-72cd35c341e1
-- title:
--   Exact centered quantum Fourier transform circuit
-- statement:
--   For every natural q>0 there exists a circuit of arbitrary one- and two-qubit gates implementing the centered discrete Fourier transform F_c defined by the source's centered coordinate convention: $$U_C=F_c,\qquad|C|\le q^2+2q+1.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5FourierCircuit.lean, lines 83–84. Uses the exact-QFT foundation by kmehltretter82, accepted Prove2Me submission 574f267d-70e8-417a-81da-58cae2f35605 (QAlgorithms.DeWolf.qft_circuit_exact), copied in Solutions/Section5QFTFoundation.lean.

import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5FourierCircuit
import Definitions.Def_Section5Verified_Section5QuadraticPhase
import Mathlib
import Theorems.Thm_section5_elementary_qft
import Theorems.Thm_section5_embed_diagonal
import Theorems.Thm_section5_linear_phase_unitary
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_elementary_centered_qft (q : ℕ) (hq : 0 < q) :
    ∃ c : Circuit gates12 q, c.size ≤ q^2+2*q+1 ∧ c.unitary=section5_centered_fourier q := by sorry
