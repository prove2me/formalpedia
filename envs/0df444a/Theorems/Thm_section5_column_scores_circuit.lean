-- Prove2me | Theorems.Thm_section5_column_scores_circuit
-- name    : section5_column_scores_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:19:06.199336+00:00
-- url     : https://prove2.me/theorems/1c40627e-1881-46f2-908f-50ae9c5a1880
-- title:
--   Circuit computing all complex column squared norms
-- statement:
--   Let a complex integer n×n matrix have signed component widths b+1 in shared data. Provide n disjoint zero score registers of width W=2n+2b+1 avoiding data and clean workspace, and a zero temporary bit outside these registers and data. A reversible circuit preserves all non-output wires and computes $$p_j'=\sum_i((\operatorname{Re}A_{ij})^2+(\operatorname{Im}A_{ij})^2),\qquad|C|\le(16W+6)\,2n^2(b+1)^2.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ColumnScoreCircuit.lean, lines 44–56. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_batched_bilinear_circuit
import Theorems.Thm_section5_signed_dot_no_overflow
import Theorems.Thm_section5_twos_complement_decode_mod
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_column_scores_circuit {m r n b : ℕ} (data : Fin r → Fin m)
    (re im : Fin n → Fin n → Fin (b+1) → Fin r)
    (p : Fin n → Fin (2*n+b+b+1) ↪ Fin m)
    (anc : Fin (2*n+b+b+1+1) ↪ Fin m) (t : Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hdata : ∀ i j e, data j ≠ p i e) (hpa : ∀ i e j, p i e ≠ anc j)
    (htp : ∀ i, t ∉ Set.range (p i)) (hta : ∀ j, t ≠ anc j) (hdt : ∀ j, data j ≠ t) :
    ∃ c : Circuit gatesRev m,
      c.size ≤ ((16*(2*n+b+b+1)+6)*((n+n)*(b+1)*(b+1)))*n ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → z' j=z j) ∧
          ∀ i, (bitsToNatLSB (z' ∘ p i):ℤ)=section5_complex_column_square re im i (z ∘ data) := by sorry
