-- Prove2me | Theorems.Thm_section5_signed_complex_matrix_product_circuit
-- name    : section5_signed_complex_matrix_product_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:22:18.915592+00:00
-- url     : https://prove2.me/theorems/7894306f-743a-41ed-874b-5d4787898cd3
-- title:
--   Exact signed complex matrix multiplication circuit
-- statement:
--   Let A,B be n×n complex integer matrices encoded with signed component widths a+1,b+1. Use 2n² pairwise disjoint zero output registers of width W=2n+a+b+1, disjoint from data and clean workspace, with a zero temporary bit outside these registers and data. A reversible circuit preserves all non-output wires and writes the exact signed real and imaginary components of AB: $$\operatorname{read}(p')=AB,\qquad|C|\le88Wn^3(a+1)(b+1).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ComplexMatrixCircuit.lean, lines 138–155. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5ComplexMatrixCircuit
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5SignedWindow
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_complex_matrix_product_circuit
import Theorems.Thm_section5_integer_matrix_product_bound
import Theorems.Thm_section5_twos_complement_decode_mod
import Theorems.Thm_section5_twos_complement_residue
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_signed_complex_matrix_product_circuit {m r n a b : ℕ}
    (data : Fin r → Fin m)
    (Are Aim : Fin n → Fin n → Fin (a+1) → Fin r)
    (Bre Bim : Fin n → Fin n → Fin (b+1) → Fin r)
    (p : Fin (2*n*n) → Fin (2*n+a+b+1) ↪ Fin m)
    (anc : Fin (2*n+a+b+1+1) ↪ Fin m) (t : Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hdata : ∀ i j e, data j ≠ p i e) (hpa : ∀ i e j, p i e ≠ anc j)
    (htp : ∀ i, t ∉ Set.range (p i)) (hta : ∀ j, t ≠ anc j) (hdt : ∀ j, data j ≠ t) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ 88*(2*n+a+b+1)*n^3*(a+1)*(b+1) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i e)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → z' j=z j) ∧
          ∀ i, section5_integer_bit_value (section5_twos_coefficient (2*n+a+b+1)) (z' ∘ p i)=
            section5_complex_product_component
              (section5_read_integer_matrix (section5_twos_coefficient (a+1)) Are Aim (z ∘ data))
              (section5_read_integer_matrix (section5_twos_coefficient (b+1)) Bre Bim (z ∘ data))
              (section5_complex_entry_index n i) := by sorry
