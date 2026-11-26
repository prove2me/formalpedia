-- Prove2me | Theorems.Thm_section5_batched_bilinear_circuit
-- name    : section5_batched_bilinear_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:15:20.070967+00:00
-- url     : https://prove2.me/theorems/c2f25714-809b-4903-aa79-95221c785b5d
-- title:
--   Batched signed bilinear arithmetic circuit
-- statement:
--   Let N weighted integer dot products each have n pairs of a-bit and b-bit factors drawn from shared data. Give each a disjoint zero w-bit output register, all outputs avoiding data, shared clean (w+1)-bit workspace and zero temporary bit; the temporary bit also avoids data and workspace. A reversible circuit preserves wires outside outputs and writes $$U(p_i')\equiv\sum_{k=1}^n\operatorname{val}_{c_{ik}}(u_{ik})\operatorname{val}_{d_{ik}}(x_{ik})\pmod{2^w},\quad|C|\le(16w+6)nabN.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5BatchedBilinearCircuit.lean, lines 12–28. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Mathlib
import Theorems.Thm_section5_clean_batch_all
import Theorems.Thm_section5_general_signed_dot_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives

theorem section5_batched_bilinear_circuit {m N r n a b w : ℕ}
    (data : Fin r → Fin m)
    (u : Fin N → Fin n → Fin a → Fin r) (x : Fin N → Fin n → Fin b → Fin r)
    (c : Fin N → Fin n → Fin a → ℤ) (d : Fin N → Fin n → Fin b → ℤ)
    (p : Fin N → Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m) (t : Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hdata : ∀ i j e, data j ≠ p i e)
    (hpa : ∀ i e j, p i e ≠ anc j)
    (htp : ∀ i, t ∉ Set.range (p i)) (hta : ∀ j, t ≠ anc j)
    (hdt : ∀ j, data j ≠ t) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ ((16*w+6)*(n*a*b))*N ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i e)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → z' j=z j) ∧
          ∀ i, (bitsToNatLSB (z' ∘ p i):ZMod (2^w))=
            ((∑ k : Fin n,section5_integer_bit_value (c i k) (z ∘ data ∘ u i k)*
              section5_integer_bit_value (d i k) (z ∘ data ∘ x i k):ℤ):ZMod (2^w)) := by sorry
