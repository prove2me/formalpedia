-- Prove2me | Theorems.Thm_section5_dyadic_vector_output_circuit
-- name    : section5_dyadic_vector_output_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:15:44.419686+00:00
-- url     : https://prove2.me/theorems/cd042cf6-f4e7-5dc3-b491-c6d07069521e
-- title:
--   Circuit output for a quantized signed dyadic vector
-- statement:
--   Let N signed (d+1)-bit source integers v_i lie in shared injective data; set r_i=2^(−S)v_i. Let f≤S and S−f+(f+2)≤d+1. Provide pairwise disjoint zero destinations of width f+2 avoiding data. There is a reversible circuit preserving other wires such that, whenever |r_i|≤1, $$\operatorname{readFp}_f(\text{dst}')=Q_f(r),\qquad|C|\le2(f+2)N,$$ with public most-significant-bit decoding.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5DyadicVectorOutput.lean, lines 96–108.

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
import Definitions.Def_Section5Verified_Section5DyadicVectorOutput
import Definitions.Def_Section5Verified_Section5FixedPointQuantization
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_dyadic_floor
import Theorems.Thm_section5_dyadic_vector_bits_circuit
import Theorems.Thm_section5_quantize_decode
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_dyadic_vector_output_circuit {m r N d S f : ℕ}
    (data : Fin r ↪ Fin m) (src : Fin N → Fin (d+1) ↪ Fin r)
    (dst : Fin N → Fin (f+2) ↪ Fin m) (hf : f ≤ S) (hfit : S-f+(f+1+1) ≤ d+1)
    (hpair : ∀ i j, i ≠ j → ∀ e b, dst i e ≠ dst j b)
    (hdata : ∀ i j e, data j ≠ dst i e) :
    ∃ c : Circuit gatesRev m, c.size ≤ 2*(f+2)*N ∧
      ∀ z : Qubits m, (∀ i e, z (dst i e)=false) →
        (∀ i, |section5_signed_dyadic_vector src S (z ∘ data) i| ≤ 1) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (dst i)) → z' j=z j) ∧
          (WithLp.toLp 2 fun i => readFp
            (⟨fun e => dst i e.rev,fun _ _ h => Fin.rev_injective ((dst i).injective h)⟩)
            f z')=section5_quantize_vector f (section5_signed_dyadic_vector src S (z ∘ data)) := by sorry
