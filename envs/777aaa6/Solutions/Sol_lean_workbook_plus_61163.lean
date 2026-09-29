-- Prove2me | solution 1 for lean_workbook_plus_61163
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:04:58.690622+00:00
-- url     : https://prove2.me/submissions/9ec710ea-21ac-4816-be88-869efde8659d

import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x : ℕ, Even x → 3 ∣ (2 ^ x - 1) := by
  intro x hx
  obtain ⟨k, rfl⟩ := hx
  have hbase : 2 ^ 2 ≡ 1 [MOD 3] := by decide
  have hp : 2 ^ (k + k) ≡ 1 [MOD 3] := by
    rw [show k + k = 2 * k by omega, pow_mul]
    simpa only [one_pow] using hbase.pow k
  exact (Nat.modEq_iff_dvd' (one_le_pow_of_one_le' (by decide : (1 : ℕ) ≤ 2) _)).mp hp.symm
