-- Prove2me | Theorems.Thm_section5_scored_column_selection_circuit
-- name    : section5_scored_column_selection_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:21:53.227938+00:00
-- url     : https://prove2.me/theorems/4db4c118-2f45-5376-a6b9-193808ff5bf9
-- title:
--   Selection of the largest scored column record
-- statement:
--   Let n=N+1 records of width R be pairwise disjoint and carry disjoint-from-score real and imaginary signed column fields of component width b+1. Put W=2n+2b+1. Assume clean zero score fields, comparison controls, arithmetic and scan workspace, and temporary bit with the source's separation hypotheses. A reversible circuit places the non-score payload of an original maximum squared-norm column in record 0, preserves wires outside records and comparison controls, and has $$|C|\le(16W+6)2n^2(b+1)^2+(16W+1+7R)N.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ScoredColumnSelection.lean, lines 54–77. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5ColumnScoreCircuit
import Definitions.Def_Section5Verified_Section5ScoredColumnSelection
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_column_scores_circuit
import Theorems.Thm_section5_maximum_record_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_scored_column_selection_circuit {m N R b : ℕ}
    (score : Fin (2*(N+1)+b+b+1) ↪ Fin R)
    (p : Fin (N+1) → Fin R ↪ Fin m)
    (re im : Fin (N+1) → Fin (b+1) → Fin R)
    (anc : Fin (2*(N+1)+b+b+1+1) ↪ Fin m) (t : Fin m)
    (ctrl : Fin N ↪ Fin m) (scanAnc : Fin 1 ↪ Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hre : ∀ i e f, re i e ≠ score f) (him : ∀ i e f, im i e ≠ score f)
    (hpa : ∀ i e j, p i e ≠ anc j) (hpt : ∀ i e, p i e ≠ t)
    (hta : ∀ j, t ≠ anc j)
    (hctrl : ∀ i j e, ctrl i ≠ p j e)
    (hscan : ∀ i e j, p i e ≠ scanAnc j) (hca : ∀ i j, ctrl i ≠ scanAnc j) :
    ∃ c : Circuit gatesRev m,
      c.size ≤ ((16*(2*(N+1)+b+b+1)+6)*(((N+1)+(N+1))*(b+1)*(b+1)))*(N+1)+
        (16*(2*(N+1)+b+b+1)+1+7*R)*N ∧
      ∀ z : Qubits m,
        z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i (score e))=false) →
        (∀ i, z (ctrl i)=false) → (∀ j, z (scanAnc j)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∃ winner : Fin (N+1),
            (∀ e, e ∉ Set.range score → z' (p 0 e)=z (p winner e)) ∧
            ∀ i, section5_record_column_square p re im i z ≤
              section5_record_column_square p re im winner z) ∧
          ∀ j, (∀ i, j ∉ Set.range (p i)) → j ∉ Set.range ctrl → z' j=z j := by sorry
