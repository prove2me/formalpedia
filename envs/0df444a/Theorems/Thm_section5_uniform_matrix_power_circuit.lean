-- Prove2me | Theorems.Thm_section5_uniform_matrix_power_circuit
-- name    : section5_uniform_matrix_power_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:35:33.539932+00:00
-- url     : https://prove2.me/theorems/92ebba69-f99e-4381-a79a-20313bea9d6a
-- title:
--   Uniform polynomial-size exact matrix-power circuit
-- statement:
--   Let n≥1, 0<ε<1 and k,f,b be the explicit decoder parameters. Embed k+1 mutually disjoint complex matrix stages with signed width b+1, clean (b+2)-bit workspace and zero temporary bit, separated as in the source. There exists a reversible circuit with $$|C|\le10^{25}(n/\varepsilon)^{13}.$$ On zero later stages, if stage 0 contains A with ‖2^(−f)op(A)−ww*‖≤1 for a real unit w, it writes the exact integer matrix A^(k+1) into the last stage, restores workspace and temporary bit, and preserves wires outside later stages.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5UniformMatrixPowerCircuit.lean, lines 12–32. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5DyadicDecoderParameters
import Definitions.Def_Section5Verified_Section5ExactMatrixPowerCircuit
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5ReconstructionPrecision
import Mathlib
import Theorems.Thm_section5_decoder_parameters_sufficient
import Theorems.Thm_section5_decoder_power_gate_bound
import Theorems.Thm_section5_dyadic_entry_bound
import Theorems.Thm_section5_exact_integer_matrix_power_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace

theorem section5_uniform_matrix_power_circuit {m n : ℕ} (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (p : Fin (section5_decoder_iterations n ε+1) → Fin (2*n*n) →
      Fin (section5_decoder_integer_width n ε+1) ↪ Fin m)
    (anc : Fin (section5_decoder_integer_width n ε+1+1) ↪ Fin m) (t : Fin m)
    (hcomponents : ∀ s i j, i ≠ j → ∀ e f, p s i e ≠ p s j f)
    (hstages : ∀ s v, s ≠ v → ∀ i j e f, p s i e ≠ p v j f)
    (hpa : ∀ s i e j, p s i e ≠ anc j) (hpt : ∀ s i e, p s i e ≠ t)
    (hta : ∀ j, t ≠ anc j) :
    ∃ circ : Circuit gatesRev m, (circ.size:ℝ) ≤ (10:ℝ)^25*((n:ℝ)/ε)^13 ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        (∀ s : Fin (section5_decoder_iterations n ε+1), 0 < s.val → ∀ i e, z (p s i e)=false) →
      ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖=1 →
        ‖(section5_signed_matrix_read (p 0) z).dyadicOperator (section5_decoder_fraction_bits n ε)-
          rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ 1 →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          section5_signed_matrix_read (p (Fin.last (section5_decoder_iterations n ε))) z'=
            (section5_signed_matrix_read (p 0) z).power (section5_decoder_iterations n ε+1) ∧
          z' t=false ∧ (∀ j, z' (anc j)=false) ∧
          ∀ j, (∀ s : Fin (section5_decoder_iterations n ε), ∀ i,
            j ∉ Set.range (p s.succ i)) → z' j=z j := by sorry
