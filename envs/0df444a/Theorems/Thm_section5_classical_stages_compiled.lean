-- Prove2me | Theorems.Thm_section5_classical_stages_compiled
-- name    : section5_classical_stages_compiled
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:45:56.060618+00:00
-- url     : https://prove2.me/theorems/915819e2-f847-51de-aac0-1a8c88c31d45
-- title:
--   Sequential compilation of classical register stages
-- statement:
--   Let K reversible circuits each have at most B gates, with pairwise disjoint stage registers p_0,…,p_K and shared clean auxiliary wires outside these registers. Suppose stage i, on zero target, writes decoded F(v_i,v_0) into p_(i+1) and preserves other wires. Starting with all later stage registers zero, their composition returns $$v_K=\operatorname{iterateLeft}(F,v_0,K),\qquad|C|\le BK,$$ restores the auxiliary wires, and preserves every wire outside the written stage registers.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5SequentialClassicalCompiler.lean, lines 97–113.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5SequentialClassicalCompiler
import Mathlib
import Theorems.Thm_section5_classical_stage_invariant
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_classical_stages_compiled {m K r a B : ℕ} {V : Type*}
    (c : Fin K → Circuit gatesRev m) (p : Fin (K+1) → Fin r → Fin m)
    (aux : Fin a → Fin m) (decode : Qubits r → V) (F : V → V → V)
    (hsize : ∀ i, (c i).size ≤ B)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (haux : ∀ i j e, aux j ≠ p i e)
    (hact : ∀ i z, (∀ j, z (aux j)=false) → (∀ e, z (p i.succ e)=false) →
      ∃ z' : Qubits m, act (c i).unitary (ket z)=ket z' ∧
        (∀ j, j ∉ Set.range (p i.succ) → z' j=z j) ∧
        decode (z' ∘ p i.succ)=F (decode (z ∘ p i.castSucc)) (decode (z ∘ p 0))) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ B*K ∧
      ∀ z : Qubits m, (∀ j, z (aux j)=false) →
        (∀ j : Fin (K+1), 0 < j.val → ∀ e, z (p j e)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          decode (z' ∘ p (Fin.last K))=section5_left_iteration F (decode (z ∘ p 0)) K ∧
          (∀ j, z' (aux j)=false) ∧
          ∀ j, (∀ i : Fin K, j ∉ Set.range (p i.succ)) → z' j=z j := by sorry
