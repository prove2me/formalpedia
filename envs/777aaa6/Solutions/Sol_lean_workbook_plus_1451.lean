-- Prove2me | solution 1 for lean_workbook_plus_1451
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:47:53.149767+00:00
-- url     : https://prove2.me/submissions/70dc018e-93bc-42f0-89d0-48f9a9d7b31b

import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.NormNum

theorem odd_sum_multiplicity (n : ℕ) (hn : Odd n) :
    emultiplicity 5 (102 ^ n + 103 ^ n) = 1 + emultiplicity 5 n := by
  have hbase : emultiplicity (5 : ℕ) (102 + 103) = (1 : ℕ∞) :=
    emultiplicity_eq_coe.mpr ⟨by decide, by decide⟩
  simpa only [hbase] using
    Nat.emultiplicity_pow_add_pow (p := 5) (by decide) (by decide)
      (x := 102) (y := 103) (by decide) (by decide) hn

theorem odd_sum_divisibility_iff (m n : ℕ) (hn : Odd n) :
    5 ^ (m + 1) ∣ 102 ^ n + 103 ^ n ↔ 5 ^ m ∣ n := by
  rw [pow_dvd_iff_le_emultiplicity, pow_dvd_iff_le_emultiplicity,
    odd_sum_multiplicity n hn]
  simp only [Nat.cast_add, Nat.cast_one, add_comm (1 : ℕ∞)]
  exact ENat.add_le_add_iff_right (by simp)

theorem solution : ¬ 5 ^ 2 ∣ 102 ^ 1991 + 103 ^ 1991 := by
  intro h
  have hd := (odd_sum_divisibility_iff 1 1991 (by decide)).mp h
  norm_num at hd
