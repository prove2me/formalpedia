-- Prove2me | Theorems.Thm_section5_twos_complement_decode_mod
-- name    : section5_twos_complement_decode_mod
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:06:00.435045+00:00
-- url     : https://prove2.me/theorems/9305c6ff-0438-5aff-a61a-aaa5645933f8
-- title:
--   Exact decoding of a bounded signed residue
-- statement:
--   Let z have b+1 bits and let v be an integer with -2^b≤v<2^b. If its unsigned little-endian value satisfies U(z)≡v modulo 2^(b+1), then its two's-complement signed value is exactly v: $$\operatorname{signed}(z)=v.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5TwosComplement.lean, lines 75–78.

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
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5SignedWindow
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_twos_complement_residue
set_option autoImplicit false
open QAlgorithms Thm49Primitives

theorem section5_twos_complement_decode_mod (b : ℕ) (z : Qubits (b+1)) (v : ℤ)
    (hmod : (bitsToNatLSB z : ZMod (2^(b+1)))=(v : ZMod (2^(b+1))))
    (hlo : -(2:ℤ)^b ≤ v) (hhi : v < (2:ℤ)^b) :
    section5_integer_bit_value (section5_twos_coefficient (b+1)) z=v := by sorry
