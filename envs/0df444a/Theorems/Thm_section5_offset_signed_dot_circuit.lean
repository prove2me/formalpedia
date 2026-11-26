-- Prove2me | Theorems.Thm_section5_offset_signed_dot_circuit
-- name    : section5_offset_signed_dot_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:15:27.008799+00:00
-- url     : https://prove2.me/theorems/28ac26e6-2789-424c-98a0-6cc933af57cd
-- title:
--   Offset-encoded signed dot-product circuit
-- statement:
--   For n offset-binary registers u_i of width a+1, n signed two's-complement registers x_i of width b+1, and a w-bit accumulator p, assume the accumulator, clean (w+1)-bit workspace and temporary bit obey the separation conditions in the source; x also avoids the workspace. A reversible circuit on zero workspace and temporary bit preserves wires outside p and satisfies $$U(p')\equiv U(p)+\sum_i(U(u_i)-2^a)\operatorname{signed}(x_i)\pmod{2^w},\quad |C|\le(16w+6)n(a+2)(b+1).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5OffsetDotCircuit.lean, lines 49–65. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5OffsetDotCircuit
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Definitions.Def_Section5Verified_Section5WeightedAccumulator
import Mathlib
import Theorems.Thm_section5_signed_integer_dot_circuit
import Theorems.Thm_section5_weighted_accumulator_circuit
import Theorems.Thm_section5_weighted_accumulator_value
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

theorem section5_offset_signed_dot_circuit {m n a b w : ℕ}
    (u : Fin n → Fin (a+1) → Fin m) (x : Fin n → Fin (b+1) → Fin m)
    (p : Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, u i j ≠ t) (hxt : ∀ i j, x i j ≠ t)
    (hup : ∀ i j, u i j ∉ Set.range p) (hxp : ∀ i j, x i j ∉ Set.range p)
    (hxa : ∀ i j k, x i j ≠ anc k) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ (16*w+6)*(n*(a+2)*(b+1)) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          (bitsToNatLSB (z' ∘ p) : ZMod (2^w))=
            (bitsToNatLSB (z ∘ p) : ZMod (2^w))+
              ((∑ i : Fin n, ((bitsToNatLSB (z ∘ u i):ℤ)-(2:ℤ)^a)*
                section5_integer_bit_value (section5_twos_coefficient (b+1)) (z ∘ x i) : ℤ) :
                  ZMod (2^w)) := by sorry
