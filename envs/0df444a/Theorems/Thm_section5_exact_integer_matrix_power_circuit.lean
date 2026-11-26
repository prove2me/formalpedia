-- Prove2me | Theorems.Thm_section5_exact_integer_matrix_power_circuit
-- name    : section5_exact_integer_matrix_power_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:30:17.254511+00:00
-- url     : https://prove2.me/theorems/c4144416-3697-5b8c-bbdf-b11d7205bcde
-- title:
--   Exact bounded integer matrix-power circuit
-- statement:
--   Let n≤2^c, (K+1)(a+c+1)<b, and let K+1 pairwise disjoint complex matrix stages have signed component width b+1. Separate them from clean (b+2)-bit workspace and a zero temporary bit. If stage 0 encodes A with every real and imaginary component bounded by 2^a and later stages are zero, a reversible circuit computes $$\operatorname{read}(p_K')=A^{K+1},\qquad|C|\le88n^3(b+1)^3K,$$ restores workspace and temporary bit, and preserves wires outside the later stages.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ExactMatrixPowerCircuit.lean, lines 43–59. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5ExactMatrixPowerCircuit
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5ModularMatrixPowers
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_fixed_width_matrix_power_circuit
import Theorems.Thm_section5_integer_matrix_bit_bound
import Theorems.Thm_section5_integer_matrix_residue_power
import Theorems.Thm_section5_twos_complement_decode_mod
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_exact_integer_matrix_power_circuit {m n b K a c : ℕ}
    (hn : n ≤ 2^c) (hwidth : (K+1)*(a+c+1) < b)
    (p : Fin (K+1) → Fin (2*n*n) → Fin (b+1) ↪ Fin m)
    (anc : Fin (b+1+1) ↪ Fin m) (t : Fin m)
    (hcomponents : ∀ s i j, i ≠ j → ∀ e f, p s i e ≠ p s j f)
    (hstages : ∀ s v, s ≠ v → ∀ i j e f, p s i e ≠ p v j f)
    (hpa : ∀ s i e j, p s i e ≠ anc j) (hpt : ∀ s i e, p s i e ≠ t)
    (hta : ∀ j, t ≠ anc j) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ (88*n^3*(b+1)^3)*K ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        (∀ s : Fin (K+1), 0 < s.val → ∀ i e, z (p s i e)=false) →
        (section5_signed_matrix_read (p 0) z).Bounded ((2:ℤ)^a) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          section5_signed_matrix_read (p (Fin.last K)) z'=
            (section5_signed_matrix_read (p 0) z).power (K+1) ∧
          z' t=false ∧ (∀ j, z' (anc j)=false) ∧
          ∀ j, (∀ s : Fin K, ∀ i, j ∉ Set.range (p s.succ i)) → z' j=z j := by sorry
