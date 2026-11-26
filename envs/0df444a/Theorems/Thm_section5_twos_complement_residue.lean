-- Prove2me | Theorems.Thm_section5_twos_complement_residue
-- name    : section5_twos_complement_residue
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:01:48.408253+00:00
-- url     : https://prove2.me/theorems/365881d5-9204-4b05-8555-702a4b9ad66c
-- title:
--   Two's-complement decoding equals the centered residue
-- statement:
--   Let $b\ge0$, let $z=(z_0,\ldots,z_b)$ be a $(b+1)$-bit least-significant-bit-first string, and let $N=\sum_{i=0}^b2^iz_i$. Write $\rho_H(u)$ for the representative of $u$ modulo $2H$ in $[-H,H)$. Then
--
--   $$
--   \sum_{i=0}^{b-1}2^iz_i-2^bz_b=\rho_{2^b}(N).
--   $$
--
--   This identifies signed binary decoding with the centered modular representation used in window arithmetic.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; this citation does not assert that the paper states the auxiliary result verbatim. Exact source: Solutions/Section5TwosComplement.lean, section5_twos_complement_residue, lines 25–48.

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
set_option autoImplicit false
open QAlgorithms Thm49Primitives

theorem section5_twos_complement_residue (b : ℕ) (z : Qubits (b+1)) :
    section5_integer_bit_value (section5_twos_coefficient (b+1)) z=
      section5_signed_residue ((2:ℤ)^b) (bitsToNatLSB z) := by sorry
