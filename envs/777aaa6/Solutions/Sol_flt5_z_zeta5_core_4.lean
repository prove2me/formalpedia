-- Prove2me | solution 4 for flt5_z_zeta5_core
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T18:31:14.730857+00:00
-- url     : https://prove2.me/submissions/8c5fbb7c-7264-4cca-8762-eb745f8c14a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Theorems.Thm_flt5_zeta5_pid_step
import Theorems.Thm_flt5_case1

-- Sketch: flt5_z_zeta5_core
-- Children: flt5_zeta5_pid_step + flt5_case1
-- Gets (p,q) from PID step, then uses case1 to find which of p,q,c1 is div by 5,
-- then rearranges to produce (a',b',c') with 5|c' and |c'| < |c|.

theorem solution (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * r ^ 5)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) :
    ∃ a' b' c' : ℤ, a' ^ 5 + b' ^ 5 = c' ^ 5 ∧ Int.gcd a' b' = 1 ∧
    (5 : ℤ) ∣ c' ∧ c' ≠ 0 ∧ c'.natAbs < c.natAbs := by
  -- Helper: k|x → k|y → k | ↑(Int.gcd x y)
  have dvd_igcd : ∀ (k x y : ℤ), k ∣ x → k ∣ y → k ∣ ↑(Int.gcd x y) := by
    intro k x y hkx hky
    have hkx' : k.natAbs ∣ x.natAbs := Int.natAbs_dvd_natAbs.mpr hkx
    have hky' : k.natAbs ∣ y.natAbs := Int.natAbs_dvd_natAbs.mpr hky
    exact Int.natAbs_dvd.mp (by exact_mod_cast Nat.dvd_gcd hkx' hky')
  -- Helper: prime ℓ, ℓ | n^5 → ℓ | n
  have prime_dvd_pow5 : ∀ (ℓ : ℕ), Nat.Prime ℓ → ∀ n : ℤ, (ℓ : ℤ) ∣ n ^ 5 → (ℓ : ℤ) ∣ n := by
    intro ℓ hℓ n hdn5
    have h := Int.natAbs_dvd_natAbs.mpr hdn5
    simp only [Int.natAbs_pow] at h
    have hnat : ℓ ∣ n.natAbs ^ 5 := by exact_mod_cast h
    exact Int.natAbs_dvd_natAbs.mp (by exact_mod_cast hℓ.dvd_of_dvd_pow hnat)
  -- Get (p,q) via the PID step
  obtain ⟨p, q, h_pq, h_cop_pq, hp_size, hq_size, hp_ne, hq_ne⟩ :=
    flt5_zeta5_pid_step a b c r s c1 h_eq h_cop h5c hc hc1 hw hPhi hcop_rs hrs
  have hc1_ne : c1 ≠ 0 := by
    intro h
    exact hc (show c = 0 by omega)
  have hsize : c1.natAbs < c.natAbs := by
    have hpos : 0 < c1.natAbs := Int.natAbs_pos.mpr hc1_ne
    have key : (c1.natAbs : ℤ) < c.natAbs := by
      rcases Int.natAbs_eq c with h1 | h1 <;>
      rcases Int.natAbs_eq c1 with h2 | h2 <;> omega
    exact_mod_cast key
  -- Helper: gcd(y, c1) = 1 from x^5+y^5=c1^5 and gcd(x,y)=1
  have gcd_with_c1 : ∀ x y : ℤ, x ^ 5 + y ^ 5 = c1 ^ 5 → Int.gcd x y = 1 →
      Int.gcd y c1 = 1 := by
    intro x y hxy hcopxy
    by_contra hne1
    obtain ⟨ℓ, hℓ_prime, hℓ_dvd_gcd⟩ := Nat.exists_prime_and_dvd hne1
    have hℓy : (ℓ : ℤ) ∣ y :=
      dvd_trans (by exact_mod_cast hℓ_dvd_gcd : (ℓ : ℤ) ∣ ↑(Int.gcd y c1))
                (Int.gcd_dvd_left y c1)
    have hℓc1 : (ℓ : ℤ) ∣ c1 :=
      dvd_trans (by exact_mod_cast hℓ_dvd_gcd : (ℓ : ℤ) ∣ ↑(Int.gcd y c1))
                (Int.gcd_dvd_right y c1)
    have hℓy5 : (ℓ : ℤ) ∣ y ^ 5 := dvd_pow hℓy (by decide)
    have hℓc15 : (ℓ : ℤ) ∣ c1 ^ 5 := dvd_pow hℓc1 (by decide)
    have hℓx5 : (ℓ : ℤ) ∣ x ^ 5 := by
      have heq : x ^ 5 = c1 ^ 5 - y ^ 5 := by omega
      rw [heq]; exact dvd_sub hℓc15 hℓy5
    have hℓx : (ℓ : ℤ) ∣ x := prime_dvd_pow5 ℓ hℓ_prime x hℓx5
    have h1 : (ℓ : ℤ) ∣ ↑(Int.gcd x y) := dvd_igcd (ℓ : ℤ) x y hℓx hℓy
    rw [hcopxy, Nat.cast_one] at h1
    have hle : (ℓ : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
    have h2 : 2 ≤ (ℓ : ℤ) := by exact_mod_cast hℓ_prime.two_le
    omega
  -- flt5_case1: 5 must divide at least one of p, q, c1
  have h_five : (5 : ℤ) ∣ p ∨ (5 : ℤ) ∣ q ∨ (5 : ℤ) ∣ c1 := by
    by_contra h
    push_neg at h
    exact flt5_case1 p q c1 h_pq h.1 h.2.1 h.2.2
  -- Sign lemmas for odd powers
  have neg_pow5 : ∀ x : ℤ, (-x) ^ 5 = -(x ^ 5) := fun x => Odd.neg_pow (by decide) x
  rcases h_five with h5p | h5q | h5c1
  · -- Case 5|p: use (q, -c1, -p) with q^5+(-c1)^5=(-p)^5
    have h_eq' : q ^ 5 + (-c1) ^ 5 = (-p) ^ 5 := by
      rw [neg_pow5, neg_pow5]; omega
    have h_cop_qc1 : Int.gcd q c1 = 1 := gcd_with_c1 p q h_pq h_cop_pq
    have h_cop' : Int.gcd q (-c1) = 1 := by
      change Nat.gcd q.natAbs (-c1).natAbs = 1
      rw [Int.natAbs_neg]; exact h_cop_qc1
    exact ⟨q, -c1, -p, h_eq', h_cop', dvd_neg.mpr h5p,
           fun h => hp_ne (neg_eq_zero.mp h),
           by rw [Int.natAbs_neg]; exact hp_size⟩
  · -- Case 5|q: use (p, -c1, -q) with p^5+(-c1)^5=(-q)^5
    have h_eq'' : p ^ 5 + (-c1) ^ 5 = (-q) ^ 5 := by
      rw [neg_pow5, neg_pow5]; omega
    have h_cop_pc1 : Int.gcd p c1 = 1 :=
      gcd_with_c1 q p (by rw [add_comm]; exact h_pq) (by rw [Int.gcd_comm]; exact h_cop_pq)
    have h_cop'' : Int.gcd p (-c1) = 1 := by
      change Nat.gcd p.natAbs (-c1).natAbs = 1
      rw [Int.natAbs_neg]; exact h_cop_pc1
    exact ⟨p, -c1, -q, h_eq'', h_cop'', dvd_neg.mpr h5q,
           fun h => hq_ne (neg_eq_zero.mp h),
           by rw [Int.natAbs_neg]; exact hq_size⟩
  · -- Case 5|c1: use (p, q, c1)
    exact ⟨p, q, c1, h_pq, h_cop_pq, h5c1, hc1_ne, hsize⟩
