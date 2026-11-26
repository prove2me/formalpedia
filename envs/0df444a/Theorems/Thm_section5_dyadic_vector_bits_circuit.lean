-- Prove2me | Theorems.Thm_section5_dyadic_vector_bits_circuit
-- name    : section5_dyadic_vector_bits_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:12:56.199615+00:00
-- url     : https://prove2.me/theorems/c67ce86c-f1fb-481e-b3c7-29783d8c78f9
-- title:
--   Parallel dyadic bit-window copying
-- statement:
--   Let N signed source registers of width d+1 lie in an injective data register. Let N destination registers of width b+1 be pairwise disjoint and avoid the data. If s+b+1≤d+1, a reversible circuit on zero destinations preserves every non-destination wire and writes $$\forall i:\ \text{dst}_i'=\operatorname{dyadicOffsetBits}_{s,b}(\text{src}_i),\qquad|C|\le2(b+1)N.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5DyadicVectorOutput.lean, lines 55–64.

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
import Definitions.Def_Section5Verified_Section5DyadicBitOutput
import Mathlib
import Theorems.Thm_section5_clean_batch_all
import Theorems.Thm_section5_dyadic_offset_bits_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_dyadic_vector_bits_circuit {m r N d b : ℕ}
    (data : Fin r ↪ Fin m) (src : Fin N → Fin (d+1) ↪ Fin r)
    (dst : Fin N → Fin (b+1) ↪ Fin m) (s : ℕ) (hfit : s+(b+1) ≤ d+1)
    (hpair : ∀ i j, i ≠ j → ∀ e f, dst i e ≠ dst j f)
    (hdata : ∀ i j e, data j ≠ dst i e) :
    ∃ c : Circuit gatesRev m, c.size ≤ 2*(b+1)*N ∧
      ∀ z : Qubits m, (∀ i e, z (dst i e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (dst i)) → z' j=z j) ∧
          ∀ i, z' ∘ dst i=section5_dyadic_offset_bits s b hfit (z ∘ data ∘ src i) := by sorry
