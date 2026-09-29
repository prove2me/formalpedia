-- Prove2me | Theorems.Thm_mme_type2_AP_hash_common_label_fiber_card
-- name    : mme_type2_AP_hash_common_label_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:11:58.890418+00:00
-- url     : https://prove2.me/theorems/8117dc5c-eb97-4c15-a8de-027d445e7711
-- title:
--   Exact common-label fiber of a linear-affine type-2 hash
-- statement:
--   Let a three-mode hash triple over $\mathbb Z/p\mathbb Z$ satisfy $H_0+H_1=2H_2$ for every state. Assume $H_0$ is a linear form in $n+1$ weight coordinates with a nonzero coefficient, and that $H_2=H_0$ is equivalent to fixing one separate affine-offset coordinate. Then the number of states for which all three hashes equal one label from a finite set $S$ is exactly $$|S|p^n.$$ This is the uniform one-edge retention count in the type-2 Salem--Spencer hash.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3, pp. 356-360; exact affine hash incidence count.

import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_finset_card

open BigOperators

set_option autoImplicit false

theorem mme_type2_AP_hash_common_label_fiber_card
    {p n : ℕ} [Fact p.Prime]
    (c : Fin (n + 1) → ZMod p) (j : Fin (n + 1)) (hc : c j ≠ 0)
    (S : Finset (ZMod p))
    (offset : (Fin (n + 1) → ZMod p) → ZMod p)
    (H : ((Fin (n + 1) → ZMod p) × ZMod p) → Fin 3 → ZMod p)
    (hAP : ∀ q, H q 0 + H q 1 = 2 * H q 2)
    (hlinear : ∀ q, H q 0 = ∑ i, c i * q.1 i)
    (haffine : ∀ q, H q 2 = H q 0 ↔ q.2 = offset q.1) :
    ((Finset.univ.filter (fun q ↦ ∃ s ∈ S, ∀ i : Fin 3, H q i = s)).card) = S.card * p ^ n := by
  sorry
