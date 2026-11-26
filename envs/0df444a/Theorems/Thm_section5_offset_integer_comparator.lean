-- Prove2me | Theorems.Thm_section5_offset_integer_comparator
-- name    : section5_offset_integer_comparator
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:19:50.59584+00:00
-- url     : https://prove2.me/theorems/325fa56d-b18a-4398-99ee-a822b6ea5f3a
-- title:
--   Offset-binary dot-product sign comparator
-- statement:
--   For n offset-binary (a+1)-bit inputs u_i and signed (b+1)-bit inputs x_i, put W=n+a+b+1. On a zero W-bit accumulator, zero (W+1)-bit workspace and zero temporary bit, with inputs separated from accumulator and temporary bit and x separated from workspace, a reversible circuit preserves all wires outside the accumulator and returns its top bit s satisfying $$s=0\iff\sum_i(U(u_i)-2^a)\operatorname{signed}(x_i)\ge0,\quad |C|\le(16W+6)n(a+2)(b+1).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5OffsetDotCircuit.lean, lines 131–146. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Theorems.Thm_section5_offset_signed_dot_circuit
import Theorems.Thm_section5_twos_complement_decode_mod
import Theorems.Thm_section5_twos_complement_residue
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

theorem section5_offset_integer_comparator {m n a b : ℕ}
    (u : Fin n → Fin (a+1) → Fin m) (x : Fin n → Fin (b+1) → Fin m)
    (p : Fin (n+a+b+1) ↪ Fin m) (anc : Fin ((n+a+b+1)+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, u i j ≠ t) (hxt : ∀ i j, x i j ≠ t)
    (hup : ∀ i j, u i j ∉ Set.range p) (hxp : ∀ i j, x i j ∉ Set.range p)
    (hxa : ∀ i j k, x i j ≠ anc k) :
    ∃ circ : Circuit gatesRev m, circ.size ≤
        (16*(n+a+b+1)+6)*(n*(a+2)*(b+1)) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i, z (p i)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          (0 ≤ ∑ i : Fin n, ((bitsToNatLSB (z ∘ u i):ℤ)-(2:ℤ)^a)*
            section5_integer_bit_value (section5_twos_coefficient (b+1)) (z ∘ x i) ↔
              z' (p (Fin.last (n+a+b)))=false) := by sorry
