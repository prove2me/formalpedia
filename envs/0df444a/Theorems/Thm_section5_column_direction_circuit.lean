-- Prove2me | Theorems.Thm_section5_column_direction_circuit
-- name    : section5_column_direction_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:29:52.547522+00:00
-- url     : https://prove2.me/theorems/6444c13a-c253-41a0-8084-48e20cb8c823
-- title:
--   Conditional direction decoding from a powered column
-- statement:
--   Let n≥1, f≤(q+1)(k+1) and (q+1)(k+1)+2≤b+1. Supply disjoint signed real/imaginary column registers A,B, zero arithmetic accumulator, workspace and temporary bit, and pairwise disjoint zero (f+2)-bit outputs separated as in the source. Put W=n+2b+2. A reversible circuit has $$|C|\le(16W+6)2n(b+1)^2+7n(b+1)+2(f+2)n.$$ If A,B encode a maximum-score column of M^(k+1), L=2^(−q)op(M) is self-adjoint, 0<ε<1, 2^(k+1)≥800n/ε, 2^f≥144n²4^(k+1)/ε, and real unit w satisfies ‖L−ww*‖≤ε/2000, then the decoded output v is nonzero and min_{s=±1}‖v/‖v‖−sw‖≤ε/6. Wires outside A,B, accumulator and outputs are preserved.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ColumnDirectionCircuit.lean, lines 11–41. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5RealCandidateCircuit
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_dyadic_decoder_output_circuit
import Theorems.Thm_section5_real_candidate_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace

theorem section5_column_direction_circuit {m n b q k f : ℕ} (hn : 1 ≤ n)
    (A B : Fin (n*(b+1)) ↪ Fin m)
    (p : Fin (n+b+b+1+1) ↪ Fin m) (anc : Fin (n+b+b+1+1+1) ↪ Fin m) (t : Fin m)
    (dst : Fin n → Fin (f+2) ↪ Fin m)
    (hf : f ≤ (q+1)*(k+1)) (hfit : (q+1)*(k+1)+2 ≤ b+1)
    (hAB : ∀ i j, A i ≠ B j)
    (hpa : ∀ i j, p i ≠ anc j) (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hAt : ∀ i, A i ≠ t) (hBt : ∀ i, B i ≠ t)
    (hAp : ∀ i, A i ∉ Set.range p) (hBp : ∀ i, B i ∉ Set.range p)
    (hpair : ∀ i j, i ≠ j → ∀ e c, dst i e ≠ dst j c)
    (hAd : ∀ i j e, A j ≠ dst i e) (hBd : ∀ i j e, B j ≠ dst i e)
    (hpd : ∀ i j e, p j ≠ dst i e) :
    ∃ c : Circuit gatesRev m,
      c.size ≤ (16*(n+b+b+1+1)+6)*((n+n)*(b+1)*(b+1))+7*(n*(b+1))+2*(f+2)*n ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        (∀ e, z (p e)=false) → (∀ i e, z (dst i e)=false) →
      ∀ (M : Section5IntegerMatrix n), IsSelfAdjoint (M.dyadicOperator q) →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        800*(n:ℝ)/ε ≤ (2:ℝ)^(k+1) →
        144*(n:ℝ)^2*(4:ℝ)^(k+1)/ε ≤ (2:ℝ)^f →
      ∀ j : Fin n, (∀ i, (M.power (k+1)).columnScore i ≤ (M.power (k+1)).columnScore j) →
        (∀ i, section5_integer_vector_read A z i=(M.power (k+1)).re i j) →
        (∀ i, section5_integer_vector_read B z i=(M.power (k+1)).im i j) →
      ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖=1 →
        ‖M.dyadicOperator q-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/2000 →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ v, v ∉ Set.range A → v ∉ Set.range B → v ∉ Set.range p →
            (∀ i, v ∉ Set.range (dst i)) → z' v=z v) ∧
          let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => readFp
            (⟨fun e => dst i e.rev,fun _ _ h => Fin.rev_injective ((dst i).injective h)⟩) f z'
          v ≠ 0 ∧ (‖NormedSpace.normalize v-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize v+w‖ ≤ ε/6) := by sorry
