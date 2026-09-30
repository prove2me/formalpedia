-- Prove2me | solution 1 for erdos_ko_rado_permutations
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:26:11.491315+00:00
-- url     : https://prove2.me/submissions/d3d7913c-6f4c-4de9-a910-8434342904f4

import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod

theorem solution (n : ℕ) (hn : 2 ≤ n) (F : Finset (Equiv.Perm (Fin n)))
    (hint : ∀ sigma ∈ F, ∀ tau ∈ F, ∃ i : Fin n, sigma i = tau i) :
    F.card ≤ (n - 1).factorial := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  letI : NeZero n := ⟨Nat.ne_of_gt hn0⟩
  let rotate : Fin n × F → Equiv.Perm (Fin n) :=
    fun p => Equiv.addLeft p.1 * p.2.val
  have hinj : Function.Injective rotate := by
    rintro ⟨a, sigma⟩ ⟨b, tau⟩ heq
    obtain ⟨i, hi⟩ := hint sigma sigma.property tau tau.property
    have hpoint := congrArg (fun p : Equiv.Perm (Fin n) => p i) heq
    change a + sigma.val i = b + tau.val i at hpoint
    rw [hi] at hpoint
    have hab : a = b := add_right_cancel hpoint
    subst b
    change Equiv.addLeft a * sigma.val = Equiv.addLeft a * tau.val at heq
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel heq))
  have hcard : n * F.card ≤ n.factorial := by
    simpa [Fintype.card_prod, Fintype.card_perm] using
      Fintype.card_le_of_injective rotate hinj
  rw [← Nat.mul_factorial_pred (Nat.ne_of_gt hn0)] at hcard
  exact Nat.le_of_mul_le_mul_left hcard hn0
