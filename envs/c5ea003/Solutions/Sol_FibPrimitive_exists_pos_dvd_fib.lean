-- Prove2me | solution 1 for FibPrimitive.exists_pos_dvd_fib
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:18:53.986805+00:00
-- url     : https://prove2.me/submissions/53ee8f00-a690-4cdd-9daa-8cbe33497984

import Mathlib
import Definitions.Def_Novelty_Primitive_Prime_Divisors_for_Composite_Index_Fibonacci_Numbers
open FibPrimitive in
theorem solution (m : ℕ) (hm : 0 < m) : ∃ n, 0 < n ∧ m ∣ Nat.fib n := by
  haveI : NeZero m := ⟨hm.ne'⟩
  set f : ℕ → ZMod m × ZMod m :=
    fun n => ((Nat.fib n : ZMod m), (Nat.fib (n + 1) : ZMod m)) with hf
  -- the Fibonacci shift is reversible, so a coincidence propagates backwards
  have hback : ∀ a b : ℕ, f (a + 1) = f (b + 1) → f a = f b := by
    intro a b h
    have h1 : ((Nat.fib (a + 1) : ZMod m)) = (Nat.fib (b + 1) : ZMod m) := by
      simpa [hf] using congrArg Prod.fst h
    have h2 : ((Nat.fib (a + 2) : ZMod m)) = (Nat.fib (b + 2) : ZMod m) := by
      simpa [hf] using congrArg Prod.snd h
    have ha : ((Nat.fib (a + 2) : ZMod m))
        = (Nat.fib a : ZMod m) + (Nat.fib (a + 1) : ZMod m) := by
      rw [Nat.fib_add_two]; push_cast; ring
    have hb : ((Nat.fib (b + 2) : ZMod m))
        = (Nat.fib b : ZMod m) + (Nat.fib (b + 1) : ZMod m) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [ha, hb, h1] at h2
    have e1 : ((Nat.fib a : ZMod m)) = (Nat.fib b : ZMod m) := add_right_cancel h2
    simp only [hf, Prod.mk.injEq]
    exact ⟨e1, h1⟩
  -- so a coincidence at distance `d` forces one at `0` and `d`
  have hshift : ∀ (d i : ℕ), f i = f (i + d) → f 0 = f d := by
    intro d i
    induction i with
    | zero => intro h; simpa using h
    | succ k ih =>
      intro h
      refine ih (hback k (k + d) ?_)
      rw [show k + d + 1 = k + 1 + d by omega]
      exact h
  -- `ZMod m × ZMod m` is finite, so `f` cannot be injective
  obtain ⟨x, y, hxy, hfe⟩ := Finite.exists_ne_map_eq_of_infinite f
  obtain ⟨a, b, hab, hfab⟩ : ∃ a b : ℕ, a < b ∧ f a = f b := by
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨x, y, h, hfe⟩
    · exact ⟨y, x, h, hfe.symm⟩
  have hstep : f a = f (a + (b - a)) := by
    rw [Nat.add_sub_cancel' hab.le]; exact hfab
  have h0 := hshift (b - a) a hstep
  refine ⟨b - a, by omega, ?_⟩
  have hz : ((Nat.fib (b - a) : ZMod m)) = 0 := by
    have := congrArg Prod.fst h0
    simpa [hf] using this.symm
  exact (ZMod.natCast_eq_zero_iff _ m).mp hz
