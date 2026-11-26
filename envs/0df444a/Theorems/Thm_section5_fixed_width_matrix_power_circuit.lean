-- Prove2me | Theorems.Thm_section5_fixed_width_matrix_power_circuit
-- name    : section5_fixed_width_matrix_power_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:27:11.048847+00:00
-- url     : https://prove2.me/theorems/99b548c5-d925-490c-99bf-c9873d780fca
-- title:
--   Fixed-width modular matrix-power circuit
-- statement:
--   Let K+1 complex n×n matrix stage registers have (b+1)-bit components, mutually disjoint across components and stages, separated from clean (b+2)-bit workspace and zero temporary bit. With stages 1 through K initially zero and initial matrix A in stage 0, a reversible circuit writes $$\operatorname{read}(p_K')=A^{K+1}\pmod{2^{b+1}},\qquad|C|\le88n^3(b+1)^3K,$$ restores workspace and temporary bit, and preserves all wires outside the later stages.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5MatrixPowerCircuit.lean, lines 49–62. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5MatrixPowerCircuit
import Definitions.Def_Section5Verified_Section5ModularMatrixPowers
import Definitions.Def_Section5Verified_Section5SequentialClassicalCompiler
import Mathlib
import Theorems.Thm_section5_classical_stages_compiled
import Theorems.Thm_section5_fixed_width_complex_matrix_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_fixed_width_matrix_power_circuit {m n b K : ℕ}
    (p : Fin (K+1) → Fin (2*n*n) → Fin (b+1) ↪ Fin m)
    (anc : Fin (b+1+1) ↪ Fin m) (t : Fin m)
    (hcomponents : ∀ s i j, i ≠ j → ∀ e f, p s i e ≠ p s j f)
    (hstages : ∀ s v, s ≠ v → ∀ i j e f, p s i e ≠ p v j f)
    (hpa : ∀ s i e j, p s i e ≠ anc j) (hpt : ∀ s i e, p s i e ≠ t)
    (hta : ∀ j, t ≠ anc j) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ (88*n^3*(b+1)^3)*K ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        (∀ s : Fin (K+1), 0 < s.val → ∀ i e, z (p s i e)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          section5_mod_matrix_read (p (Fin.last K)) z'=(section5_mod_matrix_read (p 0) z).power (K+1) ∧
          z' t=false ∧ (∀ j, z' (anc j)=false) ∧
          ∀ j, (∀ s : Fin K, ∀ i, j ∉ Set.range (p s.succ i)) → z' j=z j := by sorry
