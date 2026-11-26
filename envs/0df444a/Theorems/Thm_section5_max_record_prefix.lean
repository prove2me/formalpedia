-- Prove2me | Theorems.Thm_section5_max_record_prefix
-- name    : section5_max_record_prefix
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:49:35.948525+00:00
-- url     : https://prove2.me/theorems/e9d7d8c5-408f-411d-8cdc-08e60cf2e6f8
-- title:
--   Maximum-record invariant for a prefix of comparison stages
-- statement:
--   Let N+1 pairwise disjoint R-bit records p_i have any natural-valued score function, let N injective control wires avoid the records, and let an ancillary register start at zero. Suppose stage i, when its control and ancilla are zero, replaces p_0 by the larger-score of its current contents and p_(i+1), preserves wires outside those two records and its control, and restores the ancilla. With every control initially zero, for each k≤N the first k stages return a basis string z′ with zero ancilla, zero controls indexed i≥k, and untouched records p_j for j>k. There is an original winner j≤k with $$z'|_{p_0}=z|_{p_j},\qquad\forall i\le k:\ \operatorname{score}(z|_{p_i})\le\operatorname{score}(z|_{p_j}).$$ Wires outside all records and controls are preserved.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5MaximumRecordCircuit.lean, lines 11–29.

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
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_max_record_prefix {m N R : ℕ}
    (cs : Fin N → Circuit gatesRev m) (p : Fin (N+1) → Fin R ↪ Fin m)
    (ctrl : Fin N ↪ Fin m) (anc : Fin 1 ↪ Fin m) (score : Qubits R → ℕ)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hctrl : ∀ i j e, ctrl i ≠ p j e)
    (hact : ∀ i z, z (ctrl i)=false → (∀ j, z (anc j)=false) →
      ∃ z' : Qubits m, act (cs i).unitary (ket z)=ket z' ∧
        (z' ∘ p 0=if score (z ∘ p 0) < score (z ∘ p i.succ) then z ∘ p i.succ else z ∘ p 0) ∧
        (∀ j, j ∉ Set.range (p 0) → j ∉ Set.range (p i.succ) → j ≠ ctrl i → z' j=z j) ∧
        ∀ j, z' (anc j)=false)
    (z : Qubits m) (hzctrl : ∀ i, z (ctrl i)=false) (hzanc : ∀ j, z (anc j)=false)
    (k : ℕ) (hk : k ≤ N) :
    ∃ z' : Qubits m, act (section5_classical_stage_prefix cs k hk).unitary (ket z)=ket z' ∧
      (∀ j, z' (anc j)=false) ∧
      (∀ i : Fin N, k ≤ i.val → z' (ctrl i)=false) ∧
      (∀ j : Fin (N+1), k < j.val → z' ∘ p j=z ∘ p j) ∧
      (∃ winner : Fin (N+1), winner.val ≤ k ∧ z' ∘ p 0=z ∘ p winner ∧
        ∀ i : Fin (N+1), i.val ≤ k → score (z ∘ p i) ≤ score (z ∘ p winner)) ∧
      ∀ j, (∀ i, j ∉ Set.range (p i)) → j ∉ Set.range ctrl → z' j=z j := by sorry
