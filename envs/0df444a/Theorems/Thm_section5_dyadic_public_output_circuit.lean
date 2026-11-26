-- Prove2me | Theorems.Thm_section5_dyadic_public_output_circuit
-- name    : section5_dyadic_public_output_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:12:02.32583+00:00
-- url     : https://prove2.me/theorems/f2bf717f-18bf-5584-9662-ad7b7cee69a3
-- title:
--   Public fixed-point output from a signed integer register
-- statement:
--   Let src have signed width d+1 and dst be a disjoint zero register of width b+1, with s+b+1≤d+1. There is a reversible circuit preserving every wire outside dst such that, if v is src's signed value and −2^b≤v div 2^s<2^b, then for every fractional precision f its public most-significant-bit output satisfies $$\operatorname{readFp}_f(\text{dst}')=2^{-f}(v\mathbin{\mathrm{div}}2^s),\qquad|C|\le2(b+1).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5DyadicFixedPointDecode.lean, lines 57–68.

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
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5DyadicBitOutput
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_dyadic_offset_bits_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_dyadic_public_output_circuit {m d b : ℕ}
    (src : Fin (d+1) ↪ Fin m) (dst : Fin (b+1) ↪ Fin m) (s : ℕ)
    (hfit : s+(b+1) ≤ d+1) (hdisj : ∀ i j, src i ≠ dst j) :
    ∃ c : Circuit gatesRev m, c.size ≤ 2*(b+1) ∧
      ∀ z : Qubits m, (∀ j, z (dst j)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range dst → z' j=z j) ∧
          ∀ f : ℕ,
          -(2:ℤ)^b ≤ section5_integer_bit_value (section5_twos_coefficient (d+1)) (z ∘ src)/(2:ℤ)^s →
          section5_integer_bit_value (section5_twos_coefficient (d+1)) (z ∘ src)/(2:ℤ)^s < (2:ℤ)^b →
          readFp (⟨fun i => dst i.rev,fun _ _ h => Fin.rev_injective (dst.injective h)⟩) f z'=
            ((section5_integer_bit_value (section5_twos_coefficient (d+1)) (z ∘ src)/(2:ℤ)^s:ℤ):ℝ)/(2:ℝ)^f := by sorry
