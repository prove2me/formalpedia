-- Prove2me | Theorems.Thm_section5_dyadic_offset_bits_circuit
-- name    : section5_dyadic_offset_bits_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:08:48.301852+00:00
-- url     : https://prove2.me/theorems/d5db88eb-7582-571d-bcd1-5b9c6514b225
-- title:
--   Copying a dyadic bit window into offset output
-- statement:
--   Let src be an injective W-bit register and dst a disjoint injective (b+1)-bit register. For s+b+1≤W there is a reversible circuit which, on zero dst, writes the source's offset-encoded dyadic bit window at shift s, preserving all other wires: $$\text{dst}'=\operatorname{dyadicOffsetBits}_{s,b}(\text{src}),\qquad|C|\le2(b+1).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5DyadicBitOutput.lean, lines 58–64.

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
import Definitions.Def_Section5Verified_Section5AffineCopy
import Definitions.Def_Section5Verified_Section5DyadicBitOutput
import Mathlib
import Theorems.Thm_section5_affine_copy_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_dyadic_offset_bits_circuit {m W b : ℕ}
    (src : Fin W ↪ Fin m) (dst : Fin (b+1) ↪ Fin m) (s : ℕ) (hfit : s+(b+1) ≤ W)
    (hdisj : ∀ i j, src i ≠ dst j) :
    ∃ c : Circuit gatesRev m, c.size ≤ 2*(b+1) ∧
      ∀ z : Qubits m, (∀ j, z (dst j)=false) →
        act c.unitary (ket z)=ket (Thm410Router.updateOn dst z
          (section5_dyadic_offset_bits s b hfit (z ∘ src))) := by sorry
