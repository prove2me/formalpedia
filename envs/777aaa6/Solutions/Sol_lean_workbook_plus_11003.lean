-- Prove2me | solution 1 for lean_workbook_plus_11003
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:04:09.164074+00:00
-- url     : https://prove2.me/submissions/c7884a0a-4211-4ba8-862e-e036f173530f

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.NormNum

theorem quadratic_divisibility_residues (n : ℕ) :
    (5 ∣ 4 * n ^ 2 + 1 ∧ 13 ∣ 4 * n ^ 2 + 1) ↔
      n % 65 = 4 ∨ n % 65 = 9 ∨ n % 65 = 56 ∨ n % 65 = 61 := by
  have hcop : Nat.Coprime 5 13 := by decide
  have hboth : (5 ∣ 4 * n ^ 2 + 1 ∧ 13 ∣ 4 * n ^ 2 + 1) ↔
      65 ∣ 4 * n ^ 2 + 1 := by
    constructor
    · rintro ⟨h5, h13⟩
      exact hcop.mul_dvd_of_dvd_of_dvd h5 h13
    · intro h
      exact ⟨dvd_trans (by decide : 5 ∣ 65) h, dvd_trans (by decide : 13 ∣ 65) h⟩
  have hmod : (4 * n ^ 2 + 1) % 65 = (4 * (n % 65) ^ 2 + 1) % 65 := by
    simp only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
  have hfinite : ∀ r : Fin 65, (4 * r.val ^ 2 + 1) % 65 = 0 ↔
      r.val = 4 ∨ r.val = 9 ∨ r.val = 56 ∨ r.val = 61 := by decide
  rw [hboth, Nat.dvd_iff_mod_eq_zero, hmod]
  exact hfinite ⟨n % 65, Nat.mod_lt _ (by decide)⟩

theorem quadratic_residue_progressions (r k : ℕ)
    (hr : r = 4 ∨ r = 9 ∨ r = 56 ∨ r = 61) :
    0 < 65 * k + r ∧ 5 ∣ 4 * (65 * k + r) ^ 2 + 1 ∧
      13 ∣ 4 * (65 * k + r) ^ 2 + 1 := by
  have hrange : 0 < r ∧ r < 65 := by rcases hr with rfl | rfl | rfl | rfl <;> norm_num
  refine ⟨by omega, (quadratic_divisibility_residues _).mpr ?_⟩
  have hmod : (65 * k + r) % 65 = r := by omega
  simpa only [hmod] using hr

theorem quadratic_positive_solutions_infinite :
    {n : ℕ | 0 < n ∧ 5 ∣ 4 * n ^ 2 + 1 ∧ 13 ∣ 4 * n ^ 2 + 1}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 65 * k + 4)
  · intro a b h
    change 65 * a + 4 = 65 * b + 4 at h
    omega
  · intro k
    exact quadratic_residue_progressions 4 k (Or.inl rfl)

theorem solution : ∃ n : ℕ, 5 ∣ 4 * n ^ 2 + 1 ∧ 13 ∣ 4 * n ^ 2 + 1 := by
  obtain ⟨n, _, h5, h13⟩ := quadratic_positive_solutions_infinite.nonempty
  exact ⟨n, h5, h13⟩
