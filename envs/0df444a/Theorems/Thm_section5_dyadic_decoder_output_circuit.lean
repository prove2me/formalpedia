-- Prove2me | Theorems.Thm_section5_dyadic_decoder_output_circuit
-- name    : section5_dyadic_decoder_output_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:21:16.596041+00:00
-- url     : https://prove2.me/theorems/050389b0-82f2-5cfa-9f3e-5ea2176a6b57
-- title:
--   Conditional dyadic decoder output circuit
-- statement:
--   Let n≥1, f≤(q+1)(k+1), (q+1)(k+1)+2≤d+1. Provide n signed (d+1)-bit source registers in shared data and pairwise disjoint zero (f+2)-bit outputs avoiding data. A reversible circuit preserves all other wires with |C|≤2(f+2)n. Suppose the sources encode the larger real or imaginary column of A^(k+1) at a maximum-score column; L=2^(−q)op(A) is self-adjoint; 0<ε<1; 2^(k+1)≥800n/ε; 2^f≥144n²4^(k+1)/ε; and real unit w satisfies ‖L−ww*‖≤ε/2000. The decoded output v obeys $$v\ne0,\qquad\min_{s\in\{\pm1\}}\|v/\|v\|-sw\|\le\varepsilon/6.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5DyadicDecoderGuarantee.lean, lines 28–49.

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
import Definitions.Def_Section5Verified_Section5DyadicVectorOutput
import Definitions.Def_Section5Verified_Section5FixedPointQuantization
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_dyadic_integer_reconstruction
import Theorems.Thm_section5_dyadic_vector_output_circuit
import Theorems.Thm_section5_scaled_integer_candidate_bounds
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives ContinuousLinearMap InnerProductSpace

theorem section5_dyadic_decoder_output_circuit {m r n d q k f : ℕ} (hn : 1 ≤ n)
    (data : Fin r ↪ Fin m) (src : Fin n → Fin (d+1) ↪ Fin r)
    (dst : Fin n → Fin (f+2) ↪ Fin m)
    (hf : f ≤ (q+1)*(k+1)) (hfit : (q+1)*(k+1)+2 ≤ d+1)
    (hpair : ∀ i j, i ≠ j → ∀ e b, dst i e ≠ dst j b)
    (hdata : ∀ i j e, data j ≠ dst i e) :
    ∃ c : Circuit gatesRev m, c.size ≤ 2*(f+2)*n ∧
      ∀ (z : Qubits m), (∀ i e, z (dst i e)=false) →
      ∀ (A : Section5IntegerMatrix n), IsSelfAdjoint (A.dyadicOperator q) →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        800*(n:ℝ)/ε ≤ (2:ℝ)^(k+1) →
        144*(n:ℝ)^2*(4:ℝ)^(k+1)/ε ≤ (2:ℝ)^f →
      ∀ (j : Fin n), (∀ i, (A.power (k+1)).columnScore i ≤ (A.power (k+1)).columnScore j) →
        (∀ i, section5_integer_bit_value (section5_twos_coefficient (d+1))
          (z ∘ data ∘ src i)=(A.power (k+1)).realCandidateAt j i) →
      ∀ (w : EuclideanSpace ℝ (Fin n)), ‖w‖=1 →
        ‖A.dyadicOperator q-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/2000 →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ v, (∀ i, v ∉ Set.range (dst i)) → z' v=z v) ∧
          let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => readFp
            (⟨fun e => dst i e.rev,fun _ _ h => Fin.rev_injective ((dst i).injective h)⟩) f z'
          v ≠ 0 ∧ (‖NormedSpace.normalize v-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize v+w‖ ≤ ε/6) := by sorry
