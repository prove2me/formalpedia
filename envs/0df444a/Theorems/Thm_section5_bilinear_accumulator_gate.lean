-- Prove2me | Theorems.Thm_section5_bilinear_accumulator_gate
-- name    : section5_bilinear_accumulator_gate
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:06:01.256289+00:00
-- url     : https://prove2.me/theorems/e2e738f6-f0c5-5d6e-824f-63d91f579735
-- title:
--   A clean bilinearly controlled modular accumulator step
-- statement:
--   Let p be an injective w-bit accumulator in m wires, let anc be an injective disjoint (w+1)-bit workspace, and let t be outside p and anc. Let a,b be control wires outside p and distinct from t, and let v be natural. There exists a reversible circuit C such that, on any basis string with t and anc zero, it preserves every wire outside p, restores t and anc, and updates the unsigned little-endian accumulator value by
--
--   $$U(p')=\big(U(p)+v\mathbf1_{z_a=z_b=1}\big)\bmod2^w,\qquad |C|\le16w+6.$$
--
--   The two control wires may coincide.
-- source:
--   Original auxiliary reversible arithmetic result supporting Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5BilinearAccumulator.lean, lines 44–52; modular step definition, lines 31–33. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), copied in Solutions/Section5LcgArithmeticFoundation.lean; that foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5BilinearAccumulator
import Definitions.Def_Section5Verified_Section5ClassicalArithmeticRealization
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5EmbeddedClassicalArithmetic
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_Aux_w54_arith_ctrlAddConstInPlaceCircuit_implements
import Theorems.Thm_section5_boolean_gate_action
import Theorems.Thm_section5_controlled_add_update
import Theorems.Thm_section5_embed_reversible_clean_permutation
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

theorem section5_bilinear_accumulator_gate {m w : ℕ}
    (p : Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t a b : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hat : a ≠ t) (hbt : b ≠ t)
    (hap : a ∉ Set.range p) (hbp : b ∉ Set.range p) (v : ℕ) :
    ∃ c : Circuit gatesRev m, c.size ≤ 16*w+6 ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        act c.unitary (ket z)=ket (section5_bilinear_step p a b v z) := by sorry
