-- Prove2me | Theorems.Thm_section5_bilinear_accumulator_value
-- name    : section5_bilinear_accumulator_value
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:57.221802+00:00
-- url     : https://prove2.me/theorems/0383cc93-7587-5834-9944-4d40282280b7
-- title:
--   Unsigned value after a sequence of bilinear accumulator updates
-- statement:
--   Let p be an injective w-bit accumulator in m wires, and let L be a list of triples (a,b,v) of control wires and natural weights, with both controls of every triple outside p. For any basis string z, let E_L apply the source's successive bilinearly controlled modular additions. With U denoting unsigned little-endian decoding,
--
--   $$U(E_L(z)|_p)=\left(U(z|_p)+\sum_{(a,b,v)\in L}v\mathbf1_{z_a=z_b=1}\right)\bmod2^w.$$
--
--   The statement allows repeated controls and repeated terms.
-- source:
--   Original auxiliary modular arithmetic identity supporting Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5BilinearAccumulator.lean, lines 161–165; weighted sum definition, lines 158–159.

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
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

theorem section5_bilinear_accumulator_value {m w : ℕ}
    (p : Fin w ↪ Fin m) (ops : List (Section5BilinearTerm m))
    (hctrl : ∀ a ∈ ops, a.a ∉ Set.range p ∧ a.b ∉ Set.range p) (z : Qubits m) :
    bitsToNatLSB (section5_bilinear_eval p ops z ∘ p)=
      (bitsToNatLSB (z ∘ p)+section5_bilinear_sum ops z)%2^w := by sorry
