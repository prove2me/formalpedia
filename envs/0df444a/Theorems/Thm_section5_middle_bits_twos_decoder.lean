-- Prove2me | Theorems.Thm_section5_middle_bits_twos_decoder
-- name    : section5_middle_bits_twos_decoder
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:05:10.697433+00:00
-- url     : https://prove2.me/theorems/8d678131-62bb-4c8e-ae6c-4a9b2d1d4825
-- title:
--   Centered integer-window truncation as signed middle-bit decoding
-- statement:
--   Let z be a q-bit word and let s,b be natural numbers with s+b+1≤q−1. Let N(z) be its centered integer value, and let W_(P,H) be the source's centered integer-window truncation with P=2^s and H=2^b. Let mid be the b+1 bits beginning at little-endian position s. Then $$W_{2^s,2^b}(N(z))=2^s\operatorname{signed}_{b+1}(\mathrm{mid}).$$ The signed decoder is standard two's complement.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5TwosComplement.lean, lines 50–54.

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
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5IntegerOrientation
import Definitions.Def_Section5Verified_Section5MiddleBits
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5SignedWindow
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_twos_complement_residue
set_option autoImplicit false
open QAlgorithms Thm49Primitives

theorem section5_middle_bits_twos_decoder {q : ℕ} (z : Qubits q)
    (s b : ℕ) (h : s+(b+1) ≤ q-1) :
    section5_window_truncate ((2:ℤ)^s) ((2:ℤ)^b) (section5_centered_integer z)=
      (2:ℤ)^s*section5_integer_bit_value (section5_twos_coefficient (b+1))
        (section5_middle_bits z s (b+1) (by omega)) := by sorry
