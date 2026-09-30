-- Prove2me | solution 1 for lean_workbook_plus_46036
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:56:47.789579+00:00
-- url     : https://prove2.me/submissions/f2590dc9-71ff-4019-9f18-3909ad1434bc

import Mathlib.Data.Int.GCD
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PellThirtyOne

def orbit : ℕ → ℤ × ℤ
  | 0 => (7, 1)
  | n + 1 => (17 * (orbit n).1 + 72 * (orbit n).2,
    4 * (orbit n).1 + 17 * (orbit n).2)

theorem invariants (n : ℕ) :
    (orbit n).1 ^ 2 - 18 * (orbit n).2 ^ 2 = 31 ∧
    0 < (orbit n).1 ∧ 0 < (orbit n).2 ∧
    ∃ u v : ℤ, u * (orbit n).1 + v * (orbit n).2 = 1 := by
  induction n with
  | zero =>
    norm_num [orbit]
    exact ⟨0, 1, by norm_num⟩
  | succ n ih =>
    obtain ⟨hnorm, hx, hy, u, v, hbez⟩ := ih
    simp only [orbit]
    refine ⟨?_, by omega, by omega, 17 * u - 4 * v, -72 * u + 17 * v, ?_⟩
    · nlinarith
    · calc
        _ = u * (orbit n).1 + v * (orbit n).2 := by ring
        _ = 1 := hbez

theorem primitive (n : ℕ) : Int.gcd (orbit n).1 (orbit n).2 = 1 := by
  obtain ⟨_, _, _, u, v, hbez⟩ := invariants n
  have h : (Int.gcd (orbit n).1 (orbit n).2 : ℤ) ∣ 1 := by
    rw [← hbez]
    exact Int.dvd_add (dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) u)
      (dvd_mul_of_dvd_right (Int.gcd_dvd_right _ _) v)
  have hnat : Int.gcd (orbit n).1 (orbit n).2 ∣ 1 := by exact_mod_cast h
  exact Nat.dvd_one.mp hnat

theorem first_strictMono : StrictMono fun n => (orbit n).1 := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hx := (invariants n).2.1
  have hy := (invariants n).2.2.1
  change (orbit n).1 < 17 * (orbit n).1 + 72 * (orbit n).2
  omega

theorem injective : Function.Injective orbit := by
  intro m n h
  exact first_strictMono.injective (congrArg Prod.fst h)

theorem growth (n : ℕ) : (n : ℤ) + 7 ≤ (orbit n).1 := by
  induction n with
  | zero => norm_num [orbit]
  | succ n ih =>
    have h := first_strictMono (Nat.lt_succ_self n)
    change (orbit n).1 < (orbit (n + 1)).1 at h
    push_cast
    omega

theorem infinitely_many :
    Set.Infinite {p : ℤ × ℤ | p.1 ^ 2 - 18 * p.2 ^ 2 = 31 ∧
      0 < p.1 ∧ 0 < p.2 ∧ Int.gcd p.1 p.2 = 1} := by
  refine (Set.infinite_range_of_injective injective).mono ?_
  rintro p ⟨n, rfl⟩
  exact ⟨(invariants n).1, (invariants n).2.1, (invariants n).2.2.1, primitive n⟩

theorem arbitrarily_large (B : ℕ) :
    ∃ x y : ℤ, (B : ℤ) < x ∧ 0 < y ∧ x ^ 2 - 18 * y ^ 2 = 31 ∧ Int.gcd x y = 1 := by
  refine ⟨(orbit B).1, (orbit B).2, ?_, (invariants B).2.2.1,
    (invariants B).1, primitive B⟩
  have h := growth B
  omega

end PellThirtyOne

theorem solution : ∃ x y : ℤ, x ^ 2 - 18 * y ^ 2 = 31 := by
  exact ⟨(PellThirtyOne.orbit 0).1, (PellThirtyOne.orbit 0).2,
    (PellThirtyOne.invariants 0).1⟩
