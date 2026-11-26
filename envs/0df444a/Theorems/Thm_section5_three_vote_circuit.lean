-- Prove2me | Theorems.Thm_section5_three_vote_circuit
-- name    : section5_three_vote_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:37:27.692497+00:00
-- url     : https://prove2.me/theorems/a73a53df-14ca-5e63-bb99-b825cd88e614
-- title:
--   Circuit for three windowed label-disagreement votes
-- statement:
--   Let n≥1, 2^q≥2^40n², and let fixed-point coefficients have width a+1 and precision f. Supply three examples and label bits, three pairwise disjoint zero accumulators, shared zero workspace and temporary bit, satisfying the source's separation conditions. A reversible circuit preserves wires outside accumulators and writes each top accumulator bit as $$v_i=[\operatorname{ltf}_{u,0}(WZ_i)=-1]\mathbin{\mathrm{xor}}l_i,\qquad |C|\le3(128(n+a+34)^4+1).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ThreeVoteCircuit.lean, lines 33–51. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Definitions.Def_Section5Verified_Section5ThreeVoteCircuit
import Mathlib
import Theorems.Thm_section5_clean_batch_all
import Theorems.Thm_section5_single_qex_vote_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example

theorem section5_three_vote_circuit {m n q a : ℕ}
    (hn : 1 ≤ n) (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q) (f : ℕ)
    (ov : Fin n → Fin (a+1) ↪ Fin m) (ex : Fin 3 → Fin (n*q) ↪ Fin m)
    (label : Fin 3 ↪ Fin m)
    (p : Fin 3 → Fin (n+a+(2*section5_window_precision n+1)+1) ↪ Fin m)
    (anc : Fin (n+a+(2*section5_window_precision n+1)+1+1) ↪ Fin m) (t : Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e b, p i e ≠ p j b)
    (hpa : ∀ i e j, p i e ≠ anc j) (htp : ∀ i, t ∉ Set.range (p i)) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, ov i j ≠ t) (hxt : ∀ i j, ex i j ≠ t)
    (hup : ∀ i j k, ov i j ∉ Set.range (p k))
    (hxp : ∀ i j k, ex i j ∉ Set.range (p k))
    (hxa : ∀ i j k, ex i j ≠ anc k) (hlp : ∀ i j, label i ∉ Set.range (p j)) :
    ∃ c : Circuit gatesRev m, c.size ≤ (128*(n+a+34)^4+1)*3 ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → z' j=z j) ∧
          ∀ i, z' (p i (Fin.last (n+a+(2*section5_window_precision n+1))))=
            xor (decide (ltf (WithLp.toLp 2 fun j => readFp (ov j) f z) 0
              (section5_bounded_window_vector q (gridPoint (z ∘ ex i)))= -1)) (z (label i)) := by sorry
