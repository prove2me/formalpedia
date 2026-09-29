-- Prove2me | solution 1 for mme_ZMod_prime_affine_collision_parameter_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:49:26.49006+00:00
-- url     : https://prove2.me/submissions/af21b979-1cda-41bc-9daa-47662c3cb847

import Mathlib
import Theorems.Thm_mme_ZMod_prime_linear_hash_fiber_card

open BigOperators

set_option autoImplicit false

/-- One nontrivial linear collision equation together with a uniquely
determined affine offset leaves at most `p^n` hash-parameter pairs, even
after imposing an arbitrary additional predicate. -/
theorem solution {p n : ℕ} [hp : Fact p.Prime]
    (c : Fin (n + 1) → ZMod p) (j : Fin (n + 1)) (hc : c j ≠ 0)
    (offset : (Fin (n + 1) → ZMod p) → ZMod p)
    (P : ((Fin (n + 1) → ZMod p) × ZMod p) → Prop)
    [DecidablePred P] :
    ((Finset.univ.filter
      (fun q : (Fin (n + 1) → ZMod p) × ZMod p =>
        (∑ i, c i * q.1 i) = 0 ∧ q.2 = offset q.1 ∧ P q)).card) ≤
      p ^ n := by
  let A := Finset.univ.filter
    (fun q : (Fin (n + 1) → ZMod p) × ZMod p =>
      (∑ i, c i * q.1 i) = 0 ∧ q.2 = offset q.1 ∧ P q)
  let B := Finset.univ.filter
    (fun w : Fin (n + 1) → ZMod p => (∑ i, c i * w i) = 0)
  have hinj : Set.InjOn
      (fun q : (Fin (n + 1) → ZMod p) × ZMod p => q.1)
      (↑A : Set ((Fin (n + 1) → ZMod p) × ZMod p)) := by
    rintro ⟨w, b⟩ hwb ⟨w', b'⟩ hwb' hww'
    simp only [A, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at hwb hwb'
    change w = w' at hww'
    subst w'
    exact congrArg (fun z => (w, z))
      (hwb.2.1.trans hwb'.2.1.symm)
  have himage : A.image
      (fun q : (Fin (n + 1) → ZMod p) × ZMod p => q.1) ⊆ B := by
    intro w hw
    obtain ⟨q, hqA, rfl⟩ := Finset.mem_image.mp hw
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.mem_filter.mp hqA).2.1
  calc
    A.card = (A.image
        (fun q : (Fin (n + 1) → ZMod p) × ZMod p => q.1)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ B.card := Finset.card_le_card himage
    _ = p ^ n := mme_ZMod_prime_linear_hash_fiber_card c j hc 0
