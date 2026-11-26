-- Prove2me | Theorems.Thm_section5_fixed_width_complex_matrix_circuit
-- name    : section5_fixed_width_complex_matrix_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:23:04.137882+00:00
-- url     : https://prove2.me/theorems/8b541fd9-10be-4f96-aa3d-17f38b61683b
-- title:
--   Fixed-width modular complex matrix multiplication
-- statement:
--   Let A,B be complex n×n matrices encoded modulo 2^(b+1) in component registers. Provide pairwise disjoint zero output component registers of width b+1, separated from both inputs and clean (b+2)-bit workspace, and a zero temporary bit outside input, output and workspace. A reversible circuit preserves all non-output wires and computes $$\operatorname{read}(p')=AB\pmod{2^{b+1}},\qquad|C|\le88n^3(b+1)^3.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ModularMatrixCircuit.lean, lines 60–73. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5ModularMatrixCircuit
import Definitions.Def_Section5Verified_Section5ModularMatrixPowers
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_complex_matrix_product_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_fixed_width_complex_matrix_circuit {m n b : ℕ}
    (A B p : Fin (2*n*n) → Fin (b+1) ↪ Fin m)
    (anc : Fin (b+1+1) ↪ Fin m) (t : Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hAp : ∀ i j e f, A i e ≠ p j f) (hBp : ∀ i j e f, B i e ≠ p j f)
    (hpa : ∀ i e j, p i e ≠ anc j)
    (htp : ∀ i, t ∉ Set.range (p i)) (hta : ∀ j, t ≠ anc j)
    (hAt : ∀ i e, A i e ≠ t) (hBt : ∀ i e, B i e ≠ t) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ 88*n^3*(b+1)^3 ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i e)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → z' j=z j) ∧
          section5_mod_matrix_read p z'=
            (section5_mod_matrix_read A z).mul (section5_mod_matrix_read B z) := by sorry
