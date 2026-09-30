-- Prove2me | solution 1 for lean_workbook_plus_48772
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:57:41.656094+00:00
-- url     : https://prove2.me/submissions/733cf375-d294-4c3a-9071-dc2f0420c095

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace IntegerOrbitContraction

theorem classification (q : ℤ) (hq : 2 ≤ q.natAbs) (f : ℤ → ℤ) :
    (∀ x, (q + 1) * f x - q * f (f x) = x) ↔ f = id := by
  constructor
  · intro hf
    have step (x : ℤ) : q * (f (f x) - f x) = f x - x := by
      have := hf x
      nlinarith
    have aux : ∀ n : ℕ, ∀ x : ℤ, (f x - x).natAbs = n → f x = x := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro x hn
        by_contra hx
        have hpos : 0 < (f x - x).natAbs :=
          Int.natAbs_pos.mpr (sub_ne_zero.mpr hx)
        have habs := congrArg Int.natAbs (step x)
        rw [Int.natAbs_mul, hn] at habs
        have hnext : 0 < (f (f x) - f x).natAbs := by
          by_contra h
          have hz : (f (f x) - f x).natAbs = 0 := by omega
          rw [hz, mul_zero] at habs
          omega
        have hlt : (f (f x) - f x).natAbs < n := by nlinarith
        have hfix := ih (f (f x) - f x).natAbs hlt (f x) rfl
        have hstep := step x
        rw [hfix, sub_self, mul_zero] at hstep
        exact hx (sub_eq_zero.mp hstep.symm)
    funext x
    exact aux (f x - x).natAbs x rfl
  · rintro rfl x
    simp only [id_eq]
    ring

theorem source_classification (f : ℤ → ℤ) :
    (∀ x, 3 * f x - 2 * f (f x) = x) ↔ f = id := by
  simpa using classification 2 (by norm_num) f

theorem source_unique : ∃! f : ℤ → ℤ,
    ∀ x, 3 * f x - 2 * f (f x) = x := by
  refine ⟨id, (source_classification id).mpr rfl, ?_⟩
  exact fun f hf => (source_classification f).mp hf

end IntegerOrbitContraction

theorem solution : ∃ f : ℤ → ℤ,
    ∀ x : ℤ, 3 * f x - 2 * f (f x) = x :=
  IntegerOrbitContraction.source_unique.exists
