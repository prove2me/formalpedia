-- Prove2me | Theorems.Thm_section5_unsigned_integer_dot_circuit
-- name    : section5_unsigned_integer_dot_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:10:59.804834+00:00
-- url     : https://prove2.me/theorems/596edd95-b8fd-4a45-a48c-d49dda35608e
-- title:
--   Unsigned integer dot-product circuit
-- statement:
--   Let n pairs of unsigned registers have widths a and b. Embed a w-bit accumulator, (w+1)-bit workspace and temporary bit so that the accumulator is disjoint from the controls and workspace, and the temporary bit is outside all these registers. There is a reversible circuit preserving every wire outside the accumulator and, on zero workspace and temporary bit, satisfying $$U(p')=\left(U(p)+\sum_{i=1}^nU(u_i)U(x_i)\right)\bmod2^w,\qquad |C|\le(16w+6)nab.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5IntegerDotCircuit.lean, lines 31–44. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5IntegerDotCircuit
import Mathlib
import Theorems.Thm_section5_bilinear_accumulator_circuit
import Theorems.Thm_section5_bilinear_accumulator_value
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

theorem section5_unsigned_integer_dot_circuit {m n a b w : ℕ}
    (u : Fin n → Fin a → Fin m) (x : Fin n → Fin b → Fin m)
    (p : Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, u i j ≠ t) (hxt : ∀ i j, x i j ≠ t)
    (hup : ∀ i j, u i j ∉ Set.range p) (hxp : ∀ i j, x i j ∉ Set.range p) :
    ∃ c : Circuit gatesRev m, c.size ≤ (16*w+6)*(n*a*b) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          bitsToNatLSB (z' ∘ p)=
            (bitsToNatLSB (z ∘ p)+
              ∑ i : Fin n, bitsToNatLSB (z ∘ u i)*bitsToNatLSB (z ∘ x i))%2^w := by sorry
