-- Prove2me | Theorems.Thm_section5_scored_column_matrix_circuit
-- name    : section5_scored_column_matrix_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:26:09.753587+00:00
-- url     : https://prove2.me/theorems/d6f57278-710c-4276-8644-0aa557cf1486
-- title:
--   Matrix interpretation of scored-column selection
-- statement:
--   Let n=N+1 complex integer columns have signed width b+1 and be stored in pairwise disjoint records of width R, each with a separate zero W=2n+2b+1-bit score field. Assume zero arithmetic workspace, temporary bit, N comparison controls and scan ancilla, with the source's separation hypotheses. A reversible circuit preserves all wires outside records and comparison controls and returns a maximum-score original matrix column j in record 0, including both real and imaginary components: $$\forall i:\operatorname{score}(i)\le\operatorname{score}(j),\quad|C|\le(16W+6)2n^2(b+1)^2+(16W+1+7R)N.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ScoredColumnMatrix.lean, lines 23–48.

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
import Definitions.Def_Section5Verified_Section5RealCandidateCircuit
import Definitions.Def_Section5Verified_Section5ScoredColumnMatrix
import Definitions.Def_Section5Verified_Section5ScoredColumnSelection
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_scored_column_selection_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_scored_column_matrix_circuit {m N R b : ℕ}
    (score : Fin (2*(N+1)+b+b+1) ↪ Fin R)
    (p : Fin (N+1) → Fin R ↪ Fin m)
    (re im : Fin ((N+1)*(b+1)) ↪ Fin R)
    (anc : Fin (2*(N+1)+b+b+1+1) ↪ Fin m) (t : Fin m)
    (ctrl : Fin N ↪ Fin m) (scanAnc : Fin 1 ↪ Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hre : ∀ i f, re i ≠ score f) (him : ∀ i f, im i ≠ score f)
    (hpa : ∀ i e j, p i e ≠ anc j) (hpt : ∀ i e, p i e ≠ t) (hta : ∀ j, t ≠ anc j)
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
            (∀ i, (section5_record_integer_matrix p re im z).columnScore i ≤
              (section5_record_integer_matrix p re im z).columnScore winner) ∧
            (∀ i, section5_integer_vector_read (re.trans (p 0)) z' i=
              (section5_record_integer_matrix p re im z).re i winner) ∧
            (∀ i, section5_integer_vector_read (im.trans (p 0)) z' i=
              (section5_record_integer_matrix p re im z).im i winner)) ∧
          ∀ j, (∀ i, j ∉ Set.range (p i)) → j ∉ Set.range ctrl → z' j=z j := by sorry
