-- Prove2me | Theorems.Thm_section5_window_integer_dot_label
-- name    : section5_window_integer_dot_label
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:10:39.506482+00:00
-- url     : https://prove2.me/theorems/90e810b6-8115-42f2-816f-d60a66390ce0
-- title:
--   Windowed threshold label as an integer-dot sign
-- statement:
--   Let u_i be (a+1)-bit fixed-point coefficients with fractional precision f, let z encode n q-bit grid coordinates, and let s,b satisfy s+b+1≤q−1. Let W extract the centered middle-bit window with parameters 2^s,2^b and grid spacing √(4π/2^q), and let D(u,z) be the resulting integer dot product defined in the source. Then $$\operatorname{ltf}_{\operatorname{fp}_f(u),0}(W\operatorname{grid}(z))=\operatorname{sgn}(D(u,z)).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5WindowDotIdentity.lean, lines 62–67.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5GridPhaseMatchesQEX
import Definitions.Def_Section5Verified_Section5IntegerOrientation
import Definitions.Def_Section5Verified_Section5MiddleBits
import Definitions.Def_Section5Verified_Section5RealWindow
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5SignedWindow
import Definitions.Def_Section5Verified_Section5TwosComplement
import Definitions.Def_Section5Verified_Section5WindowDotIdentity
import Mathlib
import Theorems.Thm_section5_middle_bits_twos_decoder
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example Thm49Primitives

theorem section5_window_integer_dot_label {n q a : ℕ} (f : ℕ)
    (u : Fin n → Qubits (a+1)) (z : Qubits (n*q))
    (s b : ℕ) (h : s+(b+1) ≤ q-1) :
    ltf (WithLp.toLp 2 (fun i => fpVal (a+1) f (u i))) 0
      (section5_real_window_vec ((2:ℤ)^s) ((2:ℤ)^b) (gridSpacing (2^q)) (gridPoint z))=
        sgn (section5_window_integer_dot u z s b h : ℝ) := by sorry
