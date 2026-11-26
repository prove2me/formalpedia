-- Prove2me | Theorems.Thm_section5_signed_integer_comparator
-- name    : section5_signed_integer_comparator
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:13:49.953281+00:00
-- url     : https://prove2.me/theorems/bdecf531-ac37-5427-a112-99094ca8ab8a
-- title:
--   Sign comparison of a signed dot product
-- statement:
--   For n pairs of two's-complement registers of widths a+1 and b+1, put W=n+a+b+1. Embed a zero W-bit accumulator, zero (W+1)-bit workspace and zero temporary bit, with accumulator disjoint from inputs and workspace and temporary bit disjoint from all. A reversible circuit preserves wires outside the accumulator and returns its top bit s with $$s=0\iff\sum_i u_i x_i\ge0,\qquad |C|\le(16W+6)n(a+1)(b+1).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5SignedComparator.lean, lines 44–59. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_signed_dot_no_overflow
import Theorems.Thm_section5_signed_integer_dot_circuit
import Theorems.Thm_section5_twos_complement_decode_mod
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

theorem section5_signed_integer_comparator {m n a b : ℕ}
    (u : Fin n → Fin (a+1) → Fin m) (x : Fin n → Fin (b+1) → Fin m)
    (p : Fin (n+a+b+1) ↪ Fin m) (anc : Fin ((n+a+b+1)+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, u i j ≠ t) (hxt : ∀ i j, x i j ≠ t)
    (hup : ∀ i j, u i j ∉ Set.range p) (hxp : ∀ i j, x i j ∉ Set.range p) :
    ∃ circ : Circuit gatesRev m, circ.size ≤
        (16*(n+a+b+1)+6)*(n*(a+1)*(b+1)) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i, z (p i)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          (0 ≤ ∑ i : Fin n,
            section5_integer_bit_value (section5_twos_coefficient (a+1)) (z ∘ u i)*
            section5_integer_bit_value (section5_twos_coefficient (b+1)) (z ∘ x i) ↔
              z' (p (Fin.last (n+a+b)))=false) := by sorry
