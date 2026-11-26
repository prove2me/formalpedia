-- Prove2me | Theorems.Thm_section5_general_signed_dot_circuit
-- name    : section5_general_signed_dot_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:11:15.599095+00:00
-- url     : https://prove2.me/theorems/72c6cf0a-cfbe-4856-b70b-494ba3698525
-- title:
--   Dot products with coordinate-dependent integer bit weights
-- statement:
--   Let n pairs of a-bit and b-bit input registers have integer coefficients c_ij and d_ik. Given a w-bit accumulator disjoint from inputs and clean workspace, and a zero temporary bit outside inputs, accumulator and workspace, a reversible circuit on zero workspace preserves wires outside the accumulator and satisfies $$U(p')\equiv U(p)+\sum_i(\sum_j c_{ij}u_{ij})(\sum_kd_{ik}x_{ik})\pmod{2^w},\quad|C|\le(16w+6)nab.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5MatrixArithmeticCircuit.lean, lines 47–62. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5BilinearAccumulator
import Definitions.Def_Section5Verified_Section5MatrixArithmeticCircuit
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Mathlib
import Theorems.Thm_section5_bilinear_accumulator_circuit
import Theorems.Thm_section5_bilinear_accumulator_value
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

theorem section5_general_signed_dot_circuit {m n a b w : ℕ}
    (c : Fin n → Fin a → ℤ) (d : Fin n → Fin b → ℤ)
    (u : Fin n → Fin a → Fin m) (x : Fin n → Fin b → Fin m)
    (p : Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, u i j ≠ t) (hxt : ∀ i j, x i j ≠ t)
    (hup : ∀ i j, u i j ∉ Set.range p) (hxp : ∀ i j, x i j ∉ Set.range p) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ (16*w+6)*(n*a*b) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          (bitsToNatLSB (z' ∘ p):ZMod (2^w))=
            (bitsToNatLSB (z ∘ p):ZMod (2^w))+
              ((∑ i : Fin n,section5_integer_bit_value (c i) (z ∘ u i)*
                section5_integer_bit_value (d i) (z ∘ x i):ℤ):ZMod (2^w)) := by sorry
