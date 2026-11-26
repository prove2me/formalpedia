-- Prove2me | Theorems.Thm_section5_real_imag_selection_circuit
-- name    : section5_real_imag_selection_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:15:56.182809+00:00
-- url     : https://prove2.me/theorems/7d8e8a34-05c1-46d6-ab68-61f9cb1dad05
-- title:
--   Selecting the larger signed real or imaginary vector
-- statement:
--   Let A,B be disjoint n-component signed registers of width b+1. Put W=n+2b+2, and supply a zero W-bit accumulator, clean (W+1)-bit workspace and zero temporary bit, with inputs outside accumulator and temporary bit and accumulator disjoint from workspace. A reversible circuit replaces A by whichever original vector has larger squared norm, choosing A in ties, and preserves wires outside A,B and accumulator: $$A'=\begin{cases}B&\|A\|^2<\|B\|^2,\\A&\text{otherwise},\end{cases}\quad|C|\le(16W+6)2n(b+1)^2+7n(b+1).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5RealImagSelection.lean, lines 58–71. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5ClassicalArithmeticRealization
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5CompareSwapRecords
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Definitions.Def_Section5Verified_Section5RealImagSelection
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_Aux_w54_arith_cswapRegCircuit_implements
import Theorems.Thm_section5_embed_reversible_clean_permutation
import Theorems.Thm_section5_general_signed_dot_circuit
import Theorems.Thm_section5_record_swap_value_A
import Theorems.Thm_section5_signed_dot_no_overflow
import Theorems.Thm_section5_twos_complement_decode_mod
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

theorem section5_real_imag_selection_circuit {m n b : ℕ}
    (A B : Fin (n*(b+1)) ↪ Fin m)
    (p : Fin (n+b+b+1+1) ↪ Fin m) (anc : Fin (n+b+b+1+1+1) ↪ Fin m)
    (t : Fin m) (hAB : ∀ i j, A i ≠ B j)
    (hpa : ∀ i j, p i ≠ anc j) (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hAt : ∀ i, A i ≠ t) (hBt : ∀ i, B i ≠ t)
    (hAp : ∀ i, A i ∉ Set.range p) (hBp : ∀ i, B i ∉ Set.range p) :
    ∃ c : Circuit gatesRev m,
      c.size ≤ (16*(n+b+b+1+1)+6)*((n+n)*(b+1)*(b+1))+7*(n*(b+1)) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ e, z (p e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (z' ∘ A=if section5_signed_vector_square A z < section5_signed_vector_square B z
            then z ∘ B else z ∘ A) ∧
          ∀ j, j ∉ Set.range A → j ∉ Set.range B → j ∉ Set.range p → z' j=z j := by sorry
