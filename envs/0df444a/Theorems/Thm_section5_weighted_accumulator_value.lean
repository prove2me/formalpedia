-- Prove2me | Theorems.Thm_section5_weighted_accumulator_value
-- name    : section5_weighted_accumulator_value
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:06:06.669726+00:00
-- url     : https://prove2.me/theorems/7d1ad612-a283-40cf-a0dd-bb338f43ddde
-- title:
--   Value of a weighted accumulator
-- statement:
--   For a w-bit accumulator p, a list L of control wires outside p with natural weights c_l, and any basis string z, let E_L(z) successively add each enabled weight to p. With U denoting little-endian unsigned decoding, $$U(E_L(z)|_p)=\left(U(z|_p)+\sum_{l\in L}c_l\mathbf1_{z_l=1}\right)\bmod2^w.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5WeightedAccumulator.lean, lines 87–91. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5WeightedAccumulator
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

theorem section5_weighted_accumulator_value {m w : ℕ}
    (p : Fin w ↪ Fin m) (ops : List (Fin m × ℕ))
    (hctrl : ∀ a ∈ ops, ∀ i, a.1 ≠ p i) (z : Qubits m) :
    bitsToNatLSB (section5_weighted_eval p ops z ∘ p)=
      (bitsToNatLSB (z ∘ p)+section5_binary_weighted_sum ops z)%2^w := by sorry
