-- Prove2me | solution 1 for lean_workbook_plus_69442
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:22:28.846016+00:00
-- url     : https://prove2.me/submissions/cf262431-f121-411d-9d82-d1cb05bff968

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.ModEq

set_option autoImplicit false

theorem solution (n : ℕ) (h1 : 7 ∣ n + 1) (h2 : 191 ∣ n + 1) :
    n ≡ 1336 [ZMOD 1337] := by
  have hd : 1337 ∣ n + 1 :=
    (by decide : Nat.Coprime 7 191).mul_dvd_of_dvd_of_dvd h1 h2
  simp only [Int.ModEq]
  omega

#print axioms solution
