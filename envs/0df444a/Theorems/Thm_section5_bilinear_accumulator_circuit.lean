-- Prove2me | Theorems.Thm_section5_bilinear_accumulator_circuit
-- name    : section5_bilinear_accumulator_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:08:21.808532+00:00
-- url     : https://prove2.me/theorems/e3ec186f-e264-5830-b26f-8cae0998cabf
-- title:
--   Reversible bilinear bit accumulator
-- statement:
--   Given a w-bit accumulator p, a disjoint (w+1)-bit workspace and temporary bit t, and a list L of naturally weighted pairs of control wires outside p and t, there is a reversible circuit which, when t and the workspace start at zero, adds the sum of weights whose two controls are both one to p modulo 2^w and restores all wires outside p. The temporary bit is disjoint from the workspace. The gate bound is $$|C|\le(16w+6)|L|.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5BilinearAccumulator.lean, lines 126–135. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Mathlib
import Theorems.Thm_section5_bilinear_accumulator_gate
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

theorem section5_bilinear_accumulator_circuit {m w : ℕ}
    (p : Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (ops : List (Section5BilinearTerm m))
    (hctrl : ∀ a ∈ ops, a.a ≠ t ∧ a.b ≠ t ∧
      a.a ∉ Set.range p ∧ a.b ∉ Set.range p) :
    ∃ c : Circuit gatesRev m, c.size ≤ (16*w+6)*ops.length ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        act c.unitary (ket z)=ket (section5_bilinear_eval p ops z) := by sorry
