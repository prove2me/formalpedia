-- Prove2me | solution 1 for A166944Research.unbounded_greater_twin_primes_of_target
-- status  : ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-18T07:17:22.536936+00:00
-- url     : https://prove2.me/submissions/73958a60-753a-4322-a635-feb757b55b20

import Definitions.Def_a166944_record_core
import Mathlib.Data.Nat.Prime.Defs

/-!
Self-contained solution for the platform target
`A166944Research.unbounded_greater_twin_primes_of_target`.
-/

open A166944Research

namespace A166944Research

theorem d_add_two (n : Nat) :
    d (n + 2) = if (n + 2) % 2 = 0 then
      Nat.gcd (n + 2) (a (n + 1))
    else Nat.gcd n (a (n + 1)) := by
  simp only [d, a]
  split <;> simp_all

theorem d_add_two_of_odd (n : Nat) (h : (n + 2) % 2 ≠ 0) :
    d (n + 2) = Nat.gcd n (a (n + 1)) := by
  have h' : n % 2 ≠ 0 := by simpa using h
  simpa [h'] using d_add_two n

theorem a_pos : ∀ n : Nat, 0 < n → 0 < a n := by
  intro n
  induction n with
  | zero =>
      intro h
      cases h
  | succ n ih =>
      cases n with
      | zero => simp [a]
      | succ n =>
          intro _
          simp only [a]
          split <;> exact Nat.add_pos_left (ih (Nat.zero_lt_succ n)) _

theorem d_add_two_pos (n : Nat) : 0 < d (n + 2) := by
  rw [d_add_two]
  split <;> exact Nat.gcd_pos_of_pos_right _ (a_pos (n + 1) (Nat.zero_lt_succ n))

theorem a_add_one_le_add_two (n : Nat) : a (n + 1) ≤ a (n + 2) := by
  simp only [a]
  split <;> exact Nat.le_add_right _ _

theorem a_le_succ (n : Nat) : a n ≤ a (n + 1) := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => simpa using a_add_one_le_add_two n

theorem gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one {m n : Nat}
    (h : m % 2 = 1 ∨ n % 2 = 1) : Nat.gcd m n % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one (Nat.gcd m n) with hg | hg
  · exfalso
    have h2g : 2 ∣ Nat.gcd m n := Nat.dvd_of_mod_eq_zero hg
    rcases h with hm | hn
    · have h2m : 2 ∣ m := Nat.dvd_trans h2g (Nat.gcd_dvd_left m n)
      have hm0 : m % 2 = 0 := Nat.mod_eq_zero_of_dvd h2m
      have : (0 : Nat) = 1 := hm0.symm.trans hm
      cases this
    · have h2n : 2 ∣ n := Nat.dvd_trans h2g (Nat.gcd_dvd_right m n)
      have hn0 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h2n
      have : (0 : Nat) = 1 := hn0.symm.trans hn
      cases this
  · exact hg

theorem a_add_two_mod_two (n : Nat) :
    a (n + 2) % 2 = (n + 2) % 2 := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
      change a (n + 3) % 2 = (n + 3) % 2
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn
      · have hidx : (n + 3) % 2 ≠ 0 := by simp [Nat.add_mod, hn]
        have hprev : a (n + 2) % 2 = 0 := by
          calc
            a (n + 2) % 2 = (n + 2) % 2 := ih
            _ = 0 := by simp [hn]
        have hg : Nat.gcd (n + 1) (a (n + 2)) % 2 = 1 :=
          gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one
            (Or.inl (by simp [Nat.add_mod, hn]))
        rw [a]
        rw [if_neg hidx, Nat.add_mod]
        simp [hprev, hg, Nat.add_mod, hn]
      · have hidx : (n + 3) % 2 = 0 := by simp [Nat.add_mod, hn]
        have hprev : a (n + 2) % 2 = 1 := by
          calc
            a (n + 2) % 2 = (n + 2) % 2 := ih
            _ = 1 := by simp [hn]
        have hg : Nat.gcd (n + 3) (a (n + 2)) % 2 = 1 :=
          gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one
            (Or.inr hprev)
        rw [a]
        rw [if_pos hidx, Nat.add_mod]
        simp [hprev, hg, Nat.add_mod, hn]

theorem a_mod_two_of_two_le {n : Nat} (hn : 2 ≤ n) :
    a n % 2 = n % 2 := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using a_add_two_mod_two k

theorem d_add_two_mod_two_eq_one {n : Nat} (hn : 1 ≤ n) :
    d (n + 2) % 2 = 1 := by
  rw [d_add_two]
  rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
  · have hprev : a (n + 1) % 2 = 1 := by
      calc
        a (n + 1) % 2 = (n + 1) % 2 :=
          a_mod_two_of_two_le (Nat.succ_le_succ hn)
        _ = 1 := by simp [Nat.add_mod, hn0]
    have hg : Nat.gcd (n + 2) (a (n + 1)) % 2 = 1 :=
      gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one (Or.inr hprev)
    simp [hn0, hg]
  · have hg : Nat.gcd n (a (n + 1)) % 2 = 1 :=
      gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one (Or.inl hn1)
    simp [hn1, hg]

theorem d_mod_two_eq_one_of_three_le {n : Nat} (hn : 3 ≤ n) :
    d n % 2 = 1 := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    d_add_two_mod_two_eq_one hk

theorem d_eq_if_gcd_of_two_le {n : Nat} (hn : 2 ≤ n) :
    d n = if n % 2 = 0 then
      Nat.gcd n (a (n - 1))
    else Nat.gcd (n - 2) (a (n - 1)) := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using d_add_two k

theorem index_le_a : ∀ n : Nat, n ≤ a n := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      cases n with
      | zero => simp [a]
      | succ n =>
          rw [a]
          split
          · have hg : 1 ≤ Nat.gcd (n + 2) (a (n + 1)) :=
              Nat.succ_le_of_lt
                (Nat.gcd_pos_of_pos_right _ (a_pos (n + 1) (Nat.zero_lt_succ n)))
            exact Nat.le_trans (Nat.succ_le_succ ih)
              (Nat.add_le_add_left hg _)
          · have hg : 1 ≤ Nat.gcd n (a (n + 1)) :=
              Nat.succ_le_of_lt
                (Nat.gcd_pos_of_pos_right _ (a_pos (n + 1) (Nat.zero_lt_succ n)))
            exact Nat.le_trans (Nat.succ_le_succ ih)
              (Nat.add_le_add_left hg _)

theorem D_succ_add_one_eq_add_d (n : Nat) :
    D (n + 1) + 1 = D n + d (n + 1) := by
  simp only [D, d]
  have hindex : n ≤ a n := index_le_a n
  have hnext : n + 1 ≤ a (n + 1) := index_le_a (n + 1)
  have hstep : a n ≤ a (n + 1) := a_le_succ n
  calc
    a (n + 1) - (n + 1) + 1 =
        a (n + 1) - (n + 1) + ((n + 1) - n) := by simp
    _ = a (n + 1) - n :=
      Nat.sub_add_sub_cancel hnext (Nat.le_add_right n 1)
    _ = (a n - n) + (a (n + 1) - a n) := by
      calc
        a (n + 1) - n = (a (n + 1) - a n) + (a n - n) :=
          (Nat.sub_add_sub_cancel hstep hindex).symm
        _ = (a n - n) + (a (n + 1) - a n) := Nat.add_comm _ _

theorem one_le_d_succ (n : Nat) : 1 ≤ d (n + 1) := by
  cases n with
  | zero => simp [d, a]
  | succ n => exact Nat.succ_le_of_lt (d_add_two_pos n)

theorem D_le_succ (n : Nat) : D n ≤ D (n + 1) := by
  have hle : D n + 1 ≤ D n + d (n + 1) :=
    Nat.add_le_add_left (one_le_d_succ n) (D n)
  have hle' : D n + 1 ≤ D (n + 1) + 1 :=
    Nat.le_trans hle (Nat.le_of_eq (D_succ_add_one_eq_add_d n).symm)
  exact Nat.le_of_succ_le_succ hle'

theorem D_le_of_le {m n : Nat} (hmn : m ≤ n) : D m ≤ D n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hmn
  clear hmn
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      exact Nat.le_trans ih (by simpa [Nat.add_assoc] using D_le_succ (m + k))

theorem D_mod_two_eq_zero_of_two_le {n : Nat} (hn : 2 ≤ n) :
    D n % 2 = 0 := by
  have hsum : D n + n = a n :=
    Nat.sub_add_cancel (index_le_a n)
  rcases Nat.mod_two_eq_zero_or_one (D n) with hzero | hone
  · exact hzero
  · have hsum_mod : (D n + n) % 2 = n % 2 := by
      rw [hsum]
      exact a_mod_two_of_two_le hn
    rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
    · simp [Nat.add_mod, hone, hn0] at hsum_mod
    · simp [Nat.add_mod, hone, hn1] at hsum_mod

theorem constant_D_event_map {r C : Nat} (hr : 2 ≤ r)
    (hD : D (r - 1) = C) :
    d r = if r % 2 = 0 then Nat.gcd r (C - 1)
      else Nat.gcd (r - 2) (C + 1) := by
  have hr1 : 1 ≤ r := Nat.le_trans (by simp) hr
  have hs : 1 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hrs : r - 1 + 1 = r := Nat.sub_add_cancel hr1
  have ha : a (r - 1) = C + (r - 1) := by
    calc
      a (r - 1) = D (r - 1) + (r - 1) :=
        (Nat.sub_add_cancel (index_le_a (r - 1))).symm
      _ = C + (r - 1) := by rw [hD]
  have hC : 1 ≤ C := by
    rw [← hD]
    calc
      1 = D 1 := by simp [D, a]
      _ ≤ D (r - 1) := D_le_of_le hs
  by_cases heven : r % 2 = 0
  · rw [if_pos heven, d_eq_if_gcd_of_two_le hr, if_pos heven, ha]
    have hsum : C + (r - 1) = (C - 1) + r := by
      calc
        C + (r - 1) = ((C - 1) + 1) + (r - 1) := by
          rw [Nat.sub_add_cancel hC]
        _ = (C - 1) + ((r - 1) + 1) := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ = (C - 1) + r := by rw [hrs]
    rw [hsum]
    simpa [Nat.add_assoc] using
      (Nat.gcd_add_mul_right_right r (C - 1) 1)
  · rw [if_neg heven, d_eq_if_gcd_of_two_le hr, if_neg heven, ha]
    have hpred : r - 1 = (r - 2) + 1 := by
      apply (Nat.sub_eq_iff_eq_add hr1).2
      calc
        r = (r - 2) + 2 := (Nat.sub_add_cancel hr).symm
        _ = ((r - 2) + 1) + 1 := by simp [Nat.add_assoc]
    have hsum : C + (r - 1) = (C + 1) + (r - 2) := by
      rw [hpred]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [hsum]
    simpa [Nat.add_assoc] using
      (Nat.gcd_add_mul_right_right (r - 2) (C + 1) 1)

theorem constant_D_event_map_succ {s C : Nat} (hs : 1 ≤ s)
    (hD : D s = C) :
    d (s + 1) = if (s + 1) % 2 = 0 then Nat.gcd (s + 1) (C - 1)
      else Nat.gcd (s - 1) (C + 1) := by
  have hr : 2 ≤ s + 1 := Nat.succ_le_succ hs
  have hpred : s + 1 - 1 = s := Nat.add_sub_cancel s 1
  have hpred2 : s + 1 - 2 = s - 1 := by
    cases s with
    | zero => simp at hs
    | succ s => simp [Nat.add_assoc]
  simpa [hpred, hpred2] using constant_D_event_map hr (by simpa [hpred] using hD)

theorem a_add_d_succ {k : Nat} :
    a k + d (k + 1) = a (k + 1) := by
  have hsub : d (k + 1) = a (k + 1) - a k := by simp [d]
  rw [hsub]
  simpa [Nat.add_comm] using Nat.sub_add_cancel (a_le_succ k)

theorem a_succ_ge_add_one {k : Nat} :
    a k + 1 ≤ a (k + 1) := by
  calc
    a k + 1 ≤ a k + d (k + 1) :=
      Nat.add_le_add_left (one_le_d_succ k) _
    _ = a (k + 1) := a_add_d_succ

theorem a_lower_step {k : Nat} (hk : 2 ≤ k)
    (hbound : 2 * k ≤ a k + 2) :
    2 * (k + 1) ≤ a (k + 1) + 2 := by
  rcases Nat.eq_or_lt_of_le hbound with heq | hlt
  · have hk2 : 2 ≤ 2 * k := by
      exact Nat.le_trans (by simp) (Nat.mul_le_mul_left 2 hk)
    have ha : a k = 2 * k - 2 := by
      exact (Nat.sub_eq_iff_eq_add hk2).2 heq |>.symm
    have ha2 : a k = 2 * (k - 1) := by
      calc
        a k = 2 * k - 2 := ha
        _ = 2 * (k - 1) := by
          rw [Nat.mul_sub_left_distrib]
    have hak0 : a k % 2 = 0 := by
      have hmod := congrArg (fun x : Nat => x % 2) heq
      simpa [Nat.mul_mod, Nat.add_mod] using hmod.symm
    have hk0 : k % 2 = 0 := by
      calc
        k % 2 = a k % 2 := (a_mod_two_of_two_le hk).symm
        _ = 0 := hak0
    have hk3 : 3 ≤ k := by
      have hne2 : ¬ k = 2 := by
        intro hk2eq
        subst k
        simp [a] at heq
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hk (by
        intro h
        exact hne2 h.symm))
    have hkminus : 2 ≤ k - 1 :=
      Nat.le_sub_of_add_le (by simpa using hk3)
    have hidx : (k - 1) + 2 = k + 1 := by
      calc
        (k - 1) + 2 = (k - 1) + 1 + 1 := by simp [Nat.add_assoc]
        _ = k + 1 := by
          rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
    have hne : (k + 1) % 2 ≠ 0 := by simp [Nat.add_mod, hk0]
    have hne' : ((k - 1) + 2) % 2 ≠ 0 := by simpa [hidx] using hne
    have hdk : d (k + 1) = k - 1 := by
      calc
        d (k + 1) = d ((k - 1) + 2) := by rw [hidx]
        _ = Nat.gcd (k - 1) (a ((k - 1) + 1)) :=
          d_add_two_of_odd (k - 1) hne'
        _ = Nat.gcd (k - 1) (a k) := by
          rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
        _ = k - 1 := by
          rw [ha2]
          simpa using (Nat.gcd_mul_right 1 (k - 1) 2)
    have hd2 : 2 ≤ d (k + 1) := by simpa [hdk] using hkminus
    calc
      2 * (k + 1) = 2 * k + 2 := by simp [Nat.mul_add]
      _ = (a k + 2) + 2 := by rw [heq]
      _ ≤ (a k + d (k + 1)) + 2 := by
        exact Nat.add_le_add_right (Nat.add_le_add_left hd2 (a k)) 2
      _ = a (k + 1) + 2 := by rw [a_add_d_succ]
  · have hnext : 2 * k + 1 ≤ a k + 2 := Nat.succ_le_of_lt hlt
    have hstep : a k + 1 ≤ a (k + 1) := a_succ_ge_add_one
    calc
      2 * (k + 1) = 2 * k + 2 := by simp [Nat.mul_add]
      _ = (2 * k + 1) + 1 := by simp [Nat.add_assoc]
      _ ≤ (a k + 2) + 1 := Nat.add_le_add_right hnext 1
      _ = (a k + 1) + 2 := by simp [Nat.add_assoc, Nat.add_left_comm]
      _ ≤ a (k + 1) + 2 := Nat.add_le_add_right hstep 2

theorem two_mul_le_a_add_two {k : Nat} (hk : 2 ≤ k) :
    2 * k ≤ a k + 2 := by
  obtain ⟨t, rfl⟩ := Nat.le.dest hk
  clear hk
  induction t with
  | zero => simp [a]
  | succ t ih =>
      have ht : 2 ≤ 2 + t := Nat.le_add_right 2 t
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (a_lower_step ht ih)

private theorem add_le_next_multiple {e x H : Nat}
    (hlt : x < H) (hx : e ∣ x) (hH : e ∣ H) :
    x + e ≤ H := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hH
  have huv := Nat.succ_le_of_lt (Nat.lt_of_mul_lt_mul_left hlt)
  simpa [Nat.mul_add] using Nat.mul_le_mul_left e huv

/-- A single increment cannot cross an even multiple of its value. -/
theorem D_succ_le_even_multiple {n H : Nat} (hn : 2 ≤ n)
    (hHeven : H % 2 = 0) (hbound : D n ≤ H) (hdiv : d (n + 1) ∣ H) :
    D (n + 1) ≤ H := by
  have hupdate := D_succ_add_one_eq_add_d n
  have hepos := one_le_d_succ n
  by_cases he : d (n + 1) = 1
  · omega
  have hmap := constant_D_event_map_succ (show 1 ≤ n by omega) (rfl : D n = D n)
  by_cases hpar : (n + 1) % 2 = 0
  · rw [if_pos hpar] at hmap
    have hfactor : d (n + 1) ∣ D n - 1 := hmap.symm ▸ Nat.gcd_dvd_right _ _
    have hDtwo : 2 ≤ D n := Nat.le_trans (by decide : 2 ≤ D 2) (D_le_of_le hn)
    have hnext := add_le_next_multiple (by omega : D n - 1 < H) hfactor hdiv
    omega
  · rw [if_neg hpar] at hmap
    have hfactor : d (n + 1) ∣ D n + 1 := hmap.symm ▸ Nat.gcd_dvd_right _ _
    have hstrict : D n < H := by
      by_cases hEq : D n = H
      · have hone := Nat.dvd_sub hfactor (hEq.symm ▸ hdiv)
        have hunit : d (n + 1) ∣ 1 := by simpa using hone
        exact False.elim (he (Nat.eq_one_of_dvd_one hunit))
      · omega
    have hDeven := D_mod_two_eq_zero_of_two_le hn
    have hnext := add_le_next_multiple (by omega : D n + 1 < H) hfactor hdiv
    omega

/-- A common even multiple of the increments on an interval bounds the
horizon throughout that interval once it bounds the initial horizon. -/
theorem D_le_even_multiple_of_interval {s n H : Nat} (hs : 2 ≤ s) (hsn : s ≤ n)
    (hHeven : H % 2 = 0) (hstart : D s ≤ H)
    (hdiv : ∀ j : Nat, s < j → j ≤ n → d j ∣ H) :
    D n ≤ H := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hsn
  induction k with
  | zero => simpa using hstart
  | succ k ih =>
      have hk := ih (by omega : s ≤ s + k) (fun j hsj hj => hdiv j hsj (by omega))
      have hnext := D_succ_le_even_multiple (n := s + k) (by omega) hHeven hk
        (hdiv (s + k + 1) (by omega) (by omega))
      simpa [Nat.add_assoc] using hnext

/-- The least common multiple of 2 and the positive odd integers at most
the increment cap. Increments from index 3 onward are all odd. -/
def recordHorizonBound : Nat → Nat
  | 0 => 2
  | m + 1 =>
      if (m + 1) % 2 = 1 then Nat.lcm (m + 1) (recordHorizonBound m)
      else recordHorizonBound m

private theorem recordHorizonBound_dvd_succ (M : Nat) :
    recordHorizonBound M ∣ recordHorizonBound (M + 1) := by
  by_cases h : (M + 1) % 2 = 1
  · simpa [recordHorizonBound, h] using Nat.dvd_lcm_right (M + 1) (recordHorizonBound M)
  · simp [recordHorizonBound, h]

theorem recordHorizonBound_pos_even (M : Nat) :
    0 < recordHorizonBound M ∧ 2 ∣ recordHorizonBound M := by
  induction M with
  | zero => decide
  | succ M ih =>
      refine ⟨?_, Nat.dvd_trans ih.2 (recordHorizonBound_dvd_succ M)⟩
      by_cases h : (M + 1) % 2 = 1
      · simpa [recordHorizonBound, h] using
          Nat.lcm_pos (Nat.zero_lt_succ M) ih.1
      · simpa [recordHorizonBound, h] using ih.1

theorem odd_dvd_recordHorizonBound {e M : Nat} (he : e % 2 = 1) (hcap : e ≤ M) :
    e ∣ recordHorizonBound M := by
  induction M with
  | zero => omega
  | succ M ih =>
      by_cases h : e = M + 1
      · subst e
        simpa [recordHorizonBound, he] using Nat.dvd_lcm_left (M + 1) (recordHorizonBound M)
      · exact Nat.dvd_trans (ih (by omega)) (recordHorizonBound_dvd_succ M)

theorem D_le_recordHorizonBound_of_cap {M n : Nat} (hn : 2 ≤ n)
    (hcap : ∀ j : Nat, 2 ≤ j → j ≤ n → d j ≤ M) :
    D n ≤ recordHorizonBound M := by
  have hH := recordHorizonBound_pos_even M
  have hstart : D 2 ≤ recordHorizonBound M := by
    have htwo := Nat.le_of_dvd hH.1 hH.2
    exact Nat.le_trans (by decide : D 2 ≤ 2) htwo
  exact D_le_even_multiple_of_interval (by decide : 2 ≤ 2) hn
    (Nat.mod_eq_zero_of_dvd hH.2) hstart
    (fun j hj hle =>
      odd_dvd_recordHorizonBound (d_mod_two_eq_one_of_three_le (by omega))
        (hcap j (by omega) hle))

/-- A prefix with increments at most `M` cannot extend past this index. -/
theorem capped_prefix_index_le_recordHorizonBound_add_two {M n : Nat} (hn : 2 ≤ n)
    (hcap : ∀ j : Nat, 2 ≤ j → j ≤ n → d j ≤ M) :
    n ≤ recordHorizonBound M + 2 := by
  have hD := D_le_recordHorizonBound_of_cap hn hcap
  have ha := two_mul_le_a_add_two hn
  have heq : D n + n = a n := Nat.sub_add_cancel (index_le_a n)
  omega

private theorem record_at_or_before_of_large_increment {M n : Nat}
    (hn : 2 ≤ n) (hnew : M < d n) :
    ∃ j : Nat, 2 ≤ j ∧ j ≤ n ∧ M < d j ∧
      ∀ i : Nat, 2 ≤ i → i < j → d i < d j := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases h : ∃ j : Nat, 2 ≤ j ∧ j < n ∧ M < d j
      · obtain ⟨j, hj, hjn, hlarge⟩ := h
        obtain ⟨i, hi, hij, hilarge, hiprior⟩ := ih j hjn hj hlarge
        exact ⟨i, hi, Nat.le_trans hij (Nat.le_of_lt hjn), hilarge, hiprior⟩
      · refine ⟨n, hn, Nat.le_refl n, hnew, ?_⟩
        intro j hj hjn
        have hle : d j ≤ M := by
          by_cases hlarge : M < d j
          · exact False.elim (h ⟨j, hj, hjn, hlarge⟩)
          · omega
        exact Nat.lt_of_le_of_lt hle hnew

/-- For every threshold there is a larger difference record by an explicit
finite index in the original recurrence. -/
theorem exists_difference_record_above_by_bound (M : Nat) :
    ∃ n : Nat, 2 ≤ n ∧ n ≤ recordHorizonBound M + 3 ∧ M < d n ∧
      ∀ j : Nat, 2 ≤ j → j < n → d j < d n := by
  by_cases h : ∃ n : Nat, 2 ≤ n ∧ n ≤ recordHorizonBound M + 3 ∧ M < d n
  · obtain ⟨n, hn, hbound, hnew⟩ := h
    obtain ⟨j, hj, hjn, hjlarge, hjprior⟩ :=
      record_at_or_before_of_large_increment hn hnew
    exact ⟨j, hj, Nat.le_trans hjn hbound, hjlarge, hjprior⟩
  · have hcap : ∀ j : Nat, 2 ≤ j → j ≤ recordHorizonBound M + 3 → d j ≤ M := by
      intro j hj hle
      by_cases hlarge : M < d j
      · exact False.elim (h ⟨j, hj, hle, hlarge⟩)
      · omega
    have hindex := capped_prefix_index_le_recordHorizonBound_add_two
      (by omega : 2 ≤ recordHorizonBound M + 3) hcap
    omega

theorem difference_records_unbounded (M : Nat) :
    ∃ R : Nat, M < R ∧ IsDifferenceRecord R := by
  obtain ⟨n, hn, _, hlarge, hprior⟩ := exists_difference_record_above_by_bound M
  exact ⟨d n, hlarge, n, hn, rfl, hprior⟩

/-- The original conjecture would imply arbitrarily large twin-prime pairs. -/
theorem unbounded_greater_twin_primes_of_target (hTarget : Target) (M : ℕ) :
    ∃ R : ℕ, M < R ∧ IsGreaterTwinPrime R := by
  obtain ⟨R, hlarge, hrecord⟩ := difference_records_unbounded (M + 5)
  exact ⟨R, by omega, hTarget R (by omega) hrecord⟩

end A166944Research

open A166944Research in
theorem solution (hTarget : Target) (M : Nat) :
    ∃ R : Nat, M < R ∧ IsGreaterTwinPrime R := by
  obtain ⟨R, hlarge, hrecord⟩ := difference_records_unbounded (M + 5)
  exact ⟨R, by omega, hTarget R (by omega) hrecord⟩
