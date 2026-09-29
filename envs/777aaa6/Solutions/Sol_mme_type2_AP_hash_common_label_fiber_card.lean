-- Prove2me | solution 1 for mme_type2_AP_hash_common_label_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:13:48.781439+00:00
-- url     : https://prove2.me/submissions/c511d12f-259f-49af-9009-de3d85aa8911

import Mathlib
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_finset_card

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p n : ℕ} [Fact p.Prime]
    (c : Fin (n + 1) → ZMod p) (j : Fin (n + 1)) (hc : c j ≠ 0)
    (S : Finset (ZMod p))
    (offset : (Fin (n + 1) → ZMod p) → ZMod p)
    (H : ((Fin (n + 1) → ZMod p) × ZMod p) → Fin 3 → ZMod p)
    (hAP : ∀ q, H q 0 + H q 1 = 2 * H q 2)
    (hlinear : ∀ q, H q 0 = ∑ i, c i * q.1 i)
    (haffine : ∀ q, H q 2 = H q 0 ↔ q.2 = offset q.1) :
    ((Finset.univ.filter
      (fun q ↦ ∃ s ∈ S, ∀ i : Fin 3, H q i = s)).card) =
      S.card * p ^ n := by
  classical
  have hset :
      (Finset.univ.filter
        (fun q ↦ ∃ s ∈ S, ∀ i : Fin 3, H q i = s)) =
      Finset.univ.filter (fun q :
          (Fin (n + 1) → ZMod p) × ZMod p ↦
        (∑ i, c i * q.1 i) ∈ S ∧ q.2 = offset q.1) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨s, hs, hcommon⟩
      refine ⟨?_, ?_⟩
      · rw [← hlinear q, hcommon 0]
        exact hs
      · apply (haffine q).mp
        exact (hcommon 2).trans (hcommon 0).symm
    · rintro ⟨hmem, heq⟩
      have h20 : H q 2 = H q 0 := (haffine q).mpr heq
      have h1 : H q 1 = H q 0 := by
        have hap := hAP q
        rw [h20] at hap
        linear_combination hap
      refine ⟨H q 0, ?_, ?_⟩
      · rwa [hlinear q]
      · intro i
        fin_cases i
        · rfl
        · exact h1
        · exact h20
  rw [hset]
  exact mme_ZMod_prime_linear_hash_affine_graph_finset_card
    c j hc S offset
