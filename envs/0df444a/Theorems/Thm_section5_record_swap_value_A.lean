-- Prove2me | Theorems.Thm_section5_record_swap_value_A
-- name    : section5_record_swap_value_A
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:30.148097+00:00
-- url     : https://prove2.me/theorems/0a0682c6-088d-4a38-8929-c8251c763a39
-- title:
--   First record after an embedded controlled register swap
-- statement:
--   Let A and B be injective R-bit record embeddings into m wires, with disjoint images, and let the control wire c lie outside both records. For any basis string z, embed the source-defined controlled register swap on the concatenation of c,A,B and write its result back to those same wires, obtaining z′. The first record satisfies
--
--   $$z′|_A=\begin{cases}z|_B&z_c=1,\\z|_A&z_c=0.\end{cases}$$
--
--   The identity holds for arbitrary initial contents of both records.
-- source:
--   Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Original auxiliary record-layout identity. Exact formalization: Solutions/Section5CompareSwapRecords.lean, lines 134–139; the embedded wire layout is defined in lines 98–113. The controlled-swap arithmetic foundation is credited to Robin Kothari, accepted Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), copied in Solutions/Section5LcgArithmeticFoundation.lean.

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
import Definitions.Def_Section5Verified_Section5CompareSwapRecords
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

theorem section5_record_swap_value_A {m R : ℕ} (A B : Fin R ↪ Fin m) (ctrl : Fin m)
    (hAB : ∀ i j, A i ≠ B j) (hcA : ∀ i, ctrl ≠ A i) (hcB : ∀ i, ctrl ≠ B i)
    (z : Qubits m) :
    let e := section5_record_swap_wires A B ctrl hAB hcA hcB
    updateOn e z (cswapRegFn R (z ∘ e)) ∘ A=if z ctrl then z ∘ B else z ∘ A := by sorry
