-- Prove2me | solution 1 for mme_dwz_asymmetric_hash_retaining_states_weight_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T21:00:13.373801+00:00
-- url     : https://prove2.me/submissions/77b260f4-2f3f-4cdd-9660-110aa9a21a3f

import Theorems.Thm_mme_dwz_asymmetric_hash_retaining_states_weight_filter_card

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = levelSum)
    (mass : (Fin (N + 1) → ZMod p) → ℕ) :
    ∑ q ∈ MME.dwzAsymmetricAffineStatesRetaining
        levelSum S I J K,
        mass (fun t ↦ q.1 t.castSucc) =
      S.card * ∑ w : Fin (N + 1) → ZMod p, mass w := by
  classical
  let Weight := Fin (N + 1) → ZMod p
  let State := (Fin (N + 2) → ZMod p) × ZMod p
  let retaining : Finset State :=
    MME.dwzAsymmetricAffineStatesRetaining levelSum S I J K
  let toWeight : State → Weight := fun q t ↦ q.1 t.castSucc
  have hfiber (w : Weight) :
      (retaining.filter (fun q ↦ toWeight q = w)).card = S.card := by
    have h := mme_dwz_asymmetric_hash_retaining_states_weight_filter_card
      hpodd levelSum S I J K hsupport ({w} : Finset Weight)
    simpa only [retaining, toWeight, Finset.mem_singleton,
      Finset.card_singleton, Nat.mul_one] using h
  change ∑ q ∈ retaining, mass (toWeight q) =
    S.card * ∑ w : Weight, mass w
  rw [← Finset.sum_fiberwise retaining toWeight
    (fun q ↦ mass (toWeight q))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _hw
  calc
    ∑ q ∈ retaining with toWeight q = w, mass (toWeight q) =
        ∑ _q ∈ retaining.filter (fun q ↦ toWeight q = w), mass w := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqw : toWeight q = w :=
        (Finset.mem_filter.mp hq).2
      rw [hqw]
    _ = (retaining.filter (fun q ↦ toWeight q = w)).card * mass w := by
      exact Finset.sum_const_nat (fun _ _ ↦ rfl)
    _ = S.card * mass w := by rw [hfiber]
