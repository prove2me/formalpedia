-- Prove2me | solution 1 for mme_ZMod_prime_linear_hash_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:37:09.565025+00:00
-- url     : https://prove2.me/submissions/3b3d3b2d-a6ee-43c4-b513-1d9a1c5bd833

import Mathlib

open BigOperators

set_option autoImplicit false

/-- A nonzero linear hash from an `(n+1)`-dimensional prime field to the
field has exactly `p^n` preimages of every value. -/
theorem solution {p n : ℕ} [hp : Fact p.Prime]
    (c : Fin (n + 1) → ZMod p) (j : Fin (n + 1)) (hc : c j ≠ 0)
    (s : ZMod p) :
    ((Finset.univ.filter (fun w : Fin (n + 1) → ZMod p =>
      ∑ i, c i * w i = s)).card) = p ^ n := by
  let L : (Fin (n + 1) → ZMod p) →+ ZMod p :=
    { toFun := fun w => ∑ i, c i * w i
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] }
  have hLsurj : Function.Surjective L := by
    intro z
    let w : Fin (n + 1) → ZMod p :=
      Function.update 0 j ((c j)⁻¹ * z)
    refine ⟨w, ?_⟩
    change (∑ i, c i * w i) = z
    rw [Finset.sum_eq_single j]
    · simp [w, hc]
    · intro i _ hij
      simp [w, hij]
    · simp
  have hfiber (z : ZMod p) :
      (Finset.univ.filter (fun w : Fin (n + 1) → ZMod p => L w = z)).card =
        (Finset.univ.filter (fun w : Fin (n + 1) → ZMod p => L w = 0)).card := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range L
      (hLsurj z) (hLsurj 0)
  let C :=
    (Finset.univ.filter (fun w : Fin (n + 1) → ZMod p => L w = 0)).card
  have hpartition :
      (Finset.univ : Finset (Fin (n + 1) → ZMod p)).card =
        ∑ z : ZMod p,
          (Finset.univ.filter
            (fun w : Fin (n + 1) → ZMod p => L w = z)).card := by
    simpa only [Finset.sum_const_zero, Finset.sum_const, Finset.card_univ,
      Nat.nsmul_eq_mul, one_mul] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (Fin (n + 1) → ZMod p)))
        (t := (Finset.univ : Finset (ZMod p)))
        (f := fun w => L w) (by intro x hx; simp))
  have htotal : p ^ (n + 1) = p * C := by
    calc
      p ^ (n + 1) = Fintype.card (Fin (n + 1) → ZMod p) := by simp
      _ = ∑ z : ZMod p,
          (Finset.univ.filter
            (fun w : Fin (n + 1) → ZMod p => L w = z)).card := by
              simpa using hpartition
      _ = ∑ _z : ZMod p, C := by
        apply Finset.sum_congr rfl
        intro z _
        exact hfiber z
      _ = p * C := by simp
  have hp0 : 0 < p := hp.out.pos
  have hC : C = p ^ n := by
    rw [pow_succ'] at htotal
    exact Nat.eq_of_mul_eq_mul_left hp0 htotal.symm
  change (Finset.univ.filter
      (fun w : Fin (n + 1) → ZMod p => L w = s)).card = p ^ n
  rw [hfiber s]
  exact hC
