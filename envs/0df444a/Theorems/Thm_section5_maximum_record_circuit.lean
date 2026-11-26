-- Prove2me | Theorems.Thm_section5_maximum_record_circuit
-- name    : section5_maximum_record_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:08:02.995725+00:00
-- url     : https://prove2.me/theorems/a81267a7-f818-4e40-8915-4a69284bea8a
-- title:
--   Maximum-score record selection circuit
-- statement:
--   Let N+1 pairwise disjoint R-bit records have an injective w-bit score field, N zero comparison controls outside the records, and a clean ancilla outside records and controls. There exists a reversible circuit which puts an original maximum-score record into the first record, restores the ancilla, and preserves wires outside records and controls: $$p_0'=p_j,\quad\forall i:\operatorname{score}(p_i)\le\operatorname{score}(p_j),\quad|C|\le(16w+1+7R)N.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5MaximumRecordCircuit.lean, lines 100–111. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5SequentialClassicalCompiler
import Mathlib
import Theorems.Thm_section5_compare_swap_records_circuit
import Theorems.Thm_section5_max_record_prefix
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_maximum_record_circuit {m N R w : ℕ} (score : Fin w ↪ Fin R)
    (p : Fin (N+1) → Fin R ↪ Fin m) (ctrl : Fin N ↪ Fin m) (anc : Fin 1 ↪ Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hctrl : ∀ i j e, ctrl i ≠ p j e)
    (hanc : ∀ i e j, p i e ≠ anc j) (hca : ∀ i j, ctrl i ≠ anc j) :
    ∃ c : Circuit gatesRev m, c.size ≤ (16*w+1+7*R)*N ∧
      ∀ z : Qubits m, (∀ i, z (ctrl i)=false) → (∀ j, z (anc j)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∃ winner : Fin (N+1), z' ∘ p 0=z ∘ p winner ∧
            ∀ i, bitsToNatLSB (z ∘ p i ∘ score) ≤ bitsToNatLSB (z ∘ p winner ∘ score)) ∧
          (∀ j, z' (anc j)=false) ∧
          ∀ j, (∀ i, j ∉ Set.range (p i)) → j ∉ Set.range ctrl → z' j=z j := by sorry
