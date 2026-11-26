-- Prove2me | Theorems.Thm_section5_compare_swap_records_circuit
-- name    : section5_compare_swap_records_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:01:12.929178+00:00
-- url     : https://prove2.me/theorems/9c57520c-4015-4a62-af98-8fc6242f9465
-- title:
--   Compare-and-swap complete scored records
-- statement:
--   Let two disjoint R-bit records carry an injective w-bit unsigned score field. Give them a separate zero control and one clean ancilla. A reversible circuit places the larger-score input record in the first record, breaking ties in favor of the first input, restores the ancilla and preserves wires outside both records and control: $$A'=\begin{cases}B&\operatorname{score}(A)<\operatorname{score}(B),\\A&\text{otherwise},\end{cases}\qquad|C|\le16w+1+7R.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5CompareSwapRecords.lean, lines 199–209. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5ClassicalArithmeticRealization
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5CompareSwapRecords
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_Aux_w54_arith_cswapRegCircuit_implements
import Theorems.Thm_Aux_w54_arith_ltRegCircuit_implements
import Theorems.Thm_section5_embed_reversible_clean_permutation
import Theorems.Thm_section5_record_swap_value_A
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

theorem section5_compare_swap_records_circuit {m R w : ℕ} (score : Fin w ↪ Fin R)
    (A B : Fin R ↪ Fin m) (ctrl : Fin m) (anc : Fin 1 ↪ Fin m)
    (hAB : ∀ i j, A i ≠ B j) (hcA : ∀ i, ctrl ≠ A i) (hcB : ∀ i, ctrl ≠ B i)
    (hAa : ∀ i j, A i ≠ anc j) (hBa : ∀ i j, B i ≠ anc j) (hca : ∀ j, ctrl ≠ anc j) :
    ∃ c : Circuit gatesRev m, c.size ≤ 16*w+1+7*R ∧
      ∀ z : Qubits m, z ctrl=false → (∀ j, z (anc j)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (z' ∘ A=if bitsToNatLSB (z ∘ A ∘ score) < bitsToNatLSB (z ∘ B ∘ score)
            then z ∘ B else z ∘ A) ∧
          (∀ j, j ∉ Set.range A → j ∉ Set.range B → j ≠ ctrl → z' j=z j) ∧
          ∀ j, z' (anc j)=false := by sorry
