-- Prove2me | solution 1 for lean_workbook_plus_71300
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:20:56.473038+00:00
-- url     : https://prove2.me/submissions/a2a443ad-fa0e-4d0c-80d6-c4272c3192ca

import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

theorem solution :
    Finset.card (Finset.filter (fun k => Nat.gcd 2013 k = 1) (Finset.Icc 3 2012)) =
      1198 := by
  classical
  let F := (Finset.Icc 3 2012).filter (fun k => Nat.gcd 2013 k = 1)
  have hphi : Nat.totient 2013 = 1200 := by
    rw [show 2013 = 3 * (11 * 61) by decide,
      Nat.totient_mul (by decide : Nat.Coprime 3 (11 * 61)),
      Nat.totient_mul (by decide : Nat.Coprime 11 61),
      Nat.totient_prime (by decide : Nat.Prime 3),
      Nat.totient_prime (by decide : Nat.Prime 11),
      Nat.totient_prime (by decide : Nat.Prime 61)]
  have hset : (Finset.range 2013).filter (Nat.Coprime 2013) = insert 1 (insert 2 F) := by
    ext k
    by_cases hk : k < 3
    · interval_cases k <;> norm_num [F, Nat.Coprime]
    · simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_Icc, Nat.Coprime, F]
      omega
  have h1 : 1 ∉ insert 2 F := by simp [F]
  have h2 : 2 ∉ F := by simp [F]
  have hcard := Nat.totient_eq_card_coprime 2013
  rw [hphi, hset, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2] at hcard
  change F.card = 1198
  omega
