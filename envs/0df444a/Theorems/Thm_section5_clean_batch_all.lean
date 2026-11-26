-- Prove2me | Theorems.Thm_section5_clean_batch_all
-- name    : section5_clean_batch_all
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:42:19.220928+00:00
-- url     : https://prove2.me/theorems/dfe6a5ad-24cf-4bcb-87ae-ac630602bb21
-- title:
--   Batching clean classical circuits on disjoint outputs
-- statement:
--   Let N reversible m-wire circuits each have at most B gates and write a decoded value F_i(d) into their own initially zero w-bit register, preserving every other wire whenever a shared auxiliary register starts at zero. Assume output registers are pairwise disjoint and avoid data and auxiliary wires. Their sequential composition computes all values on the same data, preserves all wires outside the union of outputs, and satisfies $$\forall i:\ \operatorname{decode}(p_i')=F_i(d),\qquad|C|\le BN.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ClassicalBatch.lean, lines 77–91.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5ClassicalBatch
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_clean_batch_all {m N w d a B : ℕ} {V : Type*}
    (c : Fin N → Circuit gatesRev m) (p : Fin N → Fin w ↪ Fin m)
    (data : Fin d → Fin m) (aux : Fin a → Fin m)
    (hsize : ∀ i, (c i).size ≤ B)
    (hpair : ∀ i j, i ≠ j → ∀ b e, p i b ≠ p j e)
    (hdata : ∀ i j b, data j ≠ p i b) (haux : ∀ i j b, aux j ≠ p i b)
    (decode : Qubits w → V) (F : Fin N → Qubits d → V)
    (hact : ∀ i z, (∀ j, z (aux j)=false) → (∀ b, z (p i b)=false) →
      ∃ z' : Qubits m, act (c i).unitary (ket z)=ket z' ∧
        (∀ j, j ∉ Set.range (p i) → z' j=z j) ∧ decode (z' ∘ p i)=F i (z ∘ data)) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ B*N ∧
      ∀ z : Qubits m, (∀ j, z (aux j)=false) → (∀ i b, z (p i b)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → z' j=z j) ∧
          ∀ i, decode (z' ∘ p i)=F i (z ∘ data) := by sorry
