-- Prove2me | solution 1 for FibPrimitive.dvd_fib_iff_fibRank_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:23:03.964027+00:00
-- url     : https://prove2.me/submissions/de4b89af-99fe-43dd-b97c-8d91cbc67498

import Mathlib
import Definitions.Def_Novelty_Primitive_Prime_Divisors_for_Composite_Index_Fibonacci_Numbers
open FibPrimitive in
theorem solution (m : ℕ) (hm : 0 < m) (n : ℕ) :
    m ∣ Nat.fib n ↔ fibRank m ∣ n := by
  haveI : NeZero m := ⟨hm.ne'⟩
  -- the rank of apparition exists: the Fibonacci shift is reversible, so the pair
  -- sequence `(F k, F (k+1)) mod m` is purely periodic and returns to `(0, 1)`
  have hne : {n | 0 < n ∧ m ∣ Nat.fib n}.Nonempty := by
    set f : ℕ → ZMod m × ZMod m :=
      fun k => ((Nat.fib k : ZMod m), (Nat.fib (k + 1) : ZMod m)) with hf
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
    have hshift : ∀ (d i : ℕ), f i = f (i + d) → f 0 = f d := by
      intro d i
      induction i with
      | zero => intro h; simpa using h
      | succ k ih =>
        intro h
        refine ih (hback k (k + d) ?_)
        rw [show k + d + 1 = k + 1 + d by omega]
        exact h
    obtain ⟨x, y, hxy, hfe⟩ := Finite.exists_ne_map_eq_of_infinite f
    obtain ⟨a, b, hab, hfab⟩ : ∃ a b : ℕ, a < b ∧ f a = f b := by
      rcases lt_or_gt_of_ne hxy with h | h
      · exact ⟨x, y, h, hfe⟩
      · exact ⟨y, x, h, hfe.symm⟩
    have hstep : f a = f (a + (b - a)) := by
      rw [Nat.add_sub_cancel' hab.le]; exact hfab
    have h0 := hshift (b - a) a hstep
    have hz : ((Nat.fib (b - a) : ZMod m)) = 0 := by
      have := congrArg Prod.fst h0
      simpa [hf] using this.symm
    exact ⟨b - a, by omega, (ZMod.natCast_eq_zero_iff _ m).mp hz⟩
  -- `fibRank m` is the least element of that set
  have hmem : 0 < fibRank m ∧ m ∣ Nat.fib (fibRank m) := Nat.sInf_mem hne
  have hrpos : 0 < fibRank m := hmem.1
  have hrdvd : m ∣ Nat.fib (fibRank m) := hmem.2
  constructor
  · intro hdvd
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · exact dvd_zero _
    -- `fib (gcd r n) = gcd (fib r) (fib n)` is divisible by `m`, and `gcd r n > 0`,
    -- so minimality forces `gcd r n = r`
    set d := Nat.gcd (fibRank m) n with hd
    have hdpos : 0 < d := by
      refine Nat.pos_of_ne_zero fun h => ?_
      rw [hd, Nat.gcd_eq_zero_iff] at h
      omega
    have hfd : m ∣ Nat.fib d := by
      rw [hd, Nat.fib_gcd]
      exact Nat.dvd_gcd hrdvd hdvd
    have hle : fibRank m ≤ d := Nat.sInf_le ⟨hdpos, hfd⟩
    have hdr : d ∣ fibRank m := hd ▸ Nat.gcd_dvd_left _ _
    have hge : d ≤ fibRank m := Nat.le_of_dvd hrpos hdr
    have heq : d = fibRank m := le_antisymm hge hle
    exact heq ▸ (hd ▸ Nat.gcd_dvd_right (fibRank m) n)
  · intro hdvd
    exact hrdvd.trans (Nat.fib_dvd _ _ hdvd)
