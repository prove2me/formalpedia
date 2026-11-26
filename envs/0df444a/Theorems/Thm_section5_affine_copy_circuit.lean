-- Prove2me | Theorems.Thm_section5_affine_copy_circuit
-- name    : section5_affine_copy_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:06:26.475529+00:00
-- url     : https://prove2.me/theorems/85828745-a487-599c-8c86-3ffb7d721385
-- title:
--   Affine bit copying into a clean register
-- statement:
--   Let s_i be w source wires, d an injective w-wire destination disjoint from every source wire, and ν_i fixed Boolean complements. There is a reversible circuit which, for zero destination, preserves all other wires and writes $$d_i'=z_{s_i}\mathbin{\mathrm{xor}}\nu_i,\qquad |C|\le2w.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5AffineCopy.lean, lines 92–96.

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
import Definitions.Def_Section5Verified_Section5AffineCopy
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_section5_affine_copy_prefix_action
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm410Router

theorem section5_affine_copy_circuit {m w : ℕ} (src : Fin w → Fin m)
    (dst : Fin w ↪ Fin m) (neg : Fin w → Bool) (hdisj : ∀ i j, src i ≠ dst j) :
    ∃ c : Circuit gatesRev m, c.size ≤ 2*w ∧
      ∀ z : Qubits m, (∀ i, z (dst i)=false) →
        act c.unitary (ket z)=ket (updateOn dst z (section5_affine_bit src neg z)) := by sorry
