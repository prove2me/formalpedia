-- Prove2me | Theorems.Thm_section5_classical_stage_invariant
-- name    : section5_classical_stage_invariant
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:59.315807+00:00
-- url     : https://prove2.me/theorems/0cc920f9-47e3-5122-9941-d7fbd241a644
-- title:
--   Invariant for a prefix of clean classical computation stages
-- statement:
--   Let K reversible m-wire stages write into pairwise disjoint r-bit stage registers p_0,…,p_K, with auxiliary wires outside all stage registers. Suppose stage i, on zero auxiliary wires and zero target p_(i+1), preserves every non-target wire and writes decoded F(v_i,v_0). Start with zero auxiliary wires and all stages after p_0 zero. Put V_0=decode(p_0) and V_(j+1)=F(V_j,V_0). For every k≤K, the first k stages produce a basis string z′ with $$\operatorname{decode}(z'|_{p_j})=V_j\quad(j\le k),$$ while auxiliary wires remain zero, stage registers j>k remain zero, and every wire outside the later-stage targets is preserved.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5SequentialClassicalCompiler.lean, lines 33–50.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5SequentialClassicalCompiler
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_classical_stage_invariant {m K r a : ℕ} {V : Type*}
    (c : Fin K → Circuit gatesRev m) (p : Fin (K+1) → Fin r → Fin m)
    (aux : Fin a → Fin m) (decode : Qubits r → V) (F : V → V → V)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (haux : ∀ i j e, aux j ≠ p i e)
    (hact : ∀ i z, (∀ j, z (aux j)=false) → (∀ e, z (p i.succ e)=false) →
      ∃ z' : Qubits m, act (c i).unitary (ket z)=ket z' ∧
        (∀ j, j ∉ Set.range (p i.succ) → z' j=z j) ∧
        decode (z' ∘ p i.succ)=F (decode (z ∘ p i.castSucc)) (decode (z ∘ p 0)))
    (z : Qubits m) (hza : ∀ j, z (aux j)=false)
    (hz0 : ∀ j : Fin (K+1), 0 < j.val → ∀ e, z (p j e)=false)
    (k : ℕ) (hk : k ≤ K) :
    ∃ z' : Qubits m, act (section5_classical_stage_prefix c k hk).unitary (ket z)=ket z' ∧
      (∀ j, z' (aux j)=false) ∧
      (∀ j : Fin (K+1), k < j.val → ∀ e, z' (p j e)=false) ∧
      (∀ j : Fin (K+1), j.val ≤ k →
        decode (z' ∘ p j)=section5_left_iteration F (decode (z ∘ p 0)) j.val) ∧
      ∀ j, (∀ i : Fin K, j ∉ Set.range (p i.succ)) → z' j=z j := by sorry
