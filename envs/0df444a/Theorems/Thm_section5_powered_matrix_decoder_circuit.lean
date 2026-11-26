-- Prove2me | Theorems.Thm_section5_powered_matrix_decoder_circuit
-- name    : section5_powered_matrix_decoder_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:35:31.154238+00:00
-- url     : https://prove2.me/theorems/1b8f8f1a-91d4-44f8-a203-9e3a0cb950c4
-- title:
--   Conditional decoder for a supplied powered matrix
-- statement:
--   Let n=N+1, f≤(q+1)(k+1) and (q+1)(k+1)+2≤b+1. Supply disjoint R-bit column records encoding M^(k+1), zero score fields, scan controls, arithmetic workspace, and n zero output registers of width f+2, with all separation hypotheses in the source. There is a reversible circuit of size at most $$ (16W+6)2n^2(b+1)^2+(16W+1+7R)N+(16V+6)2n(b+1)^2+7n(b+1)+2(f+2)n,$$ where W=2n+2b+1 and V=n+2b+2. If L=2^(−q)op(M) is self-adjoint, 0<ε<1, 2^(k+1)≥800n/ε, 2^f≥144n²4^(k+1)/ε and real unit w has ‖L−ww*‖≤ε/2000, its decoded output v satisfies v≠0 and min_{s=±1}‖v/‖v‖−sw‖≤ε/6.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5PoweredMatrixDecoder.lean, lines 16–59. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5PoweredMatrixDecoder
import Definitions.Def_Section5Verified_Section5RealCandidateCircuit
import Definitions.Def_Section5Verified_Section5ScoredColumnMatrix
import Mathlib
import Theorems.Thm_section5_column_direction_circuit
import Theorems.Thm_section5_scored_column_matrix_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace

theorem section5_powered_matrix_decoder_circuit {m N R b q k f : ℕ}
    (score : Fin (2*(N+1)+b+b+1) ↪ Fin R)
    (p : Fin (N+1) → Fin R ↪ Fin m) (re im : Fin ((N+1)*(b+1)) ↪ Fin R)
    (anc : Fin (2*(N+1)+b+b+1+1) ↪ Fin m) (t : Fin m)
    (ctrl : Fin N ↪ Fin m) (scanAnc : Fin 1 ↪ Fin m)
    (np : Fin ((N+1)+b+b+1+1) ↪ Fin m)
    (na : Fin ((N+1)+b+b+1+1+1) ↪ Fin m) (nt : Fin m)
    (dst : Fin (N+1) → Fin (f+2) ↪ Fin m)
    (hf : f ≤ (q+1)*(k+1)) (hfit : (q+1)*(k+1)+2 ≤ b+1)
    (hpair : ∀ i j, i ≠ j → ∀ e g, p i e ≠ p j g)
    (hre : ∀ i e, re i ≠ score e) (him : ∀ i e, im i ≠ score e)
    (hri : ∀ i j, re i ≠ im j)
    (hpa : ∀ i e j, p i e ≠ anc j) (hpt : ∀ i e, p i e ≠ t) (hta : ∀ j, t ≠ anc j)
    (hctrl : ∀ i j e, ctrl i ≠ p j e)
    (hscan : ∀ i e j, p i e ≠ scanAnc j) (hca : ∀ i j, ctrl i ≠ scanAnc j)
    (hnpa : ∀ i j, np i ≠ na j) (hntp : nt ∉ Set.range np) (hnta : ∀ j, nt ≠ na j)
    (hdst : ∀ i j, i ≠ j → ∀ e g, dst i e ≠ dst j g)
    (hndst : ∀ i j e, np j ≠ dst i e)
    (hnpf : ∀ e, section5_outside_column_records p ctrl (np e))
    (hnaf : ∀ e, section5_outside_column_records p ctrl (na e))
    (hntf : section5_outside_column_records p ctrl nt)
    (hdf : ∀ i e, section5_outside_column_records p ctrl (dst i e)) :
    ∃ c : Circuit gatesRev m,
      c.size ≤
        (((16*(2*(N+1)+b+b+1)+6)*(((N+1)+(N+1))*(b+1)*(b+1)))*(N+1)+
          (16*(2*(N+1)+b+b+1)+1+7*R)*N)+
        ((16*((N+1)+b+b+1+1)+6)*(((N+1)+(N+1))*(b+1)*(b+1))+
          7*((N+1)*(b+1))+2*(f+2)*(N+1)) ∧
      ∀ z : Qubits m,
        z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i (score e))=false) →
        (∀ i, z (ctrl i)=false) → (∀ j, z (scanAnc j)=false) →
        z nt=false → (∀ j, z (na j)=false) → (∀ e, z (np e)=false) →
        (∀ i e, z (dst i e)=false) →
      ∀ (M : Section5IntegerMatrix (N+1)), IsSelfAdjoint (M.dyadicOperator q) →
        section5_record_integer_matrix p re im z=M.power (k+1) →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        800*((N+1:ℕ):ℝ)/ε ≤ (2:ℝ)^(k+1) →
        144*((N+1:ℕ):ℝ)^2*(4:ℝ)^(k+1)/ε ≤ (2:ℝ)^f →
      ∀ w : EuclideanSpace ℝ (Fin (N+1)), ‖w‖=1 →
        ‖M.dyadicOperator q-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/2000 →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          let v : EuclideanSpace ℝ (Fin (N+1)) := WithLp.toLp 2 fun i => readFp
            (⟨fun e => dst i e.rev,fun _ _ h => Fin.rev_injective ((dst i).injective h)⟩) f z'
          v ≠ 0 ∧ (‖NormedSpace.normalize v-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize v+w‖ ≤ ε/6) := by sorry
