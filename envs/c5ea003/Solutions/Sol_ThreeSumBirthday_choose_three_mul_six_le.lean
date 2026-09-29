-- Prove2me | solution 1 for ThreeSumBirthday.choose_three_mul_six_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T03:49:57.663318+00:00
-- url     : https://prove2.me/submissions/01e0b43b-8776-4b3e-810e-f54ad0dc5f58

/-
# `ThreeSumBirthday.choose_three_mul_six_le`
Target `01575308` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

`6 · C(n,3) = n(n−1)(n−2)`, and each factor is at most `n`, so the product is at most `n³`.
For `n < 3` the binomial coefficient is `0` and the bound is trivial.

NOTE: the tactic routes below are NOT yet probe-verified (the build lock was held when this was
drafted), hence the `first | ... | ...` alternatives. If all fail, the next step is a `trace_state`
probe rather than another guessed rewrite — that is the discipline this session had to learn.
-/
import Mathlib
import Definitions.Def_Speculative_AutoResearch_ThreeSumBirthdayHierarchy

set_option autoImplicit false

/-- **The target, verbatim.** -/
theorem solution : ∀ n : ℕ, n.choose 3 * 6 ≤ n * n * n := by
  intro n
  -- CONFIRMED by probe: `n.descFactorial 3 = n*(n-1)*(n-2)` closes by simp+ring.
  -- There is NO `Nat.choose_three_right` (only `choose_two_right`); the route is via descFactorial.
  have h6 : Nat.factorial 3 = 6 := by decide
  have hd : n.choose 3 * 6 = n.descFactorial 3 := by
    rw [Nat.choose_eq_descFactorial_div_factorial, ← h6]
    exact Nat.div_mul_cancel (Nat.factorial_dvd_descFactorial n 3)
  have he : n.descFactorial 3 = n * (n - 1) * (n - 2) := by
    simp [Nat.descFactorial]
    ring
  rw [hd, he]
  have h1 : n - 1 ≤ n := Nat.sub_le _ _
  have h2 : n - 2 ≤ n := Nat.sub_le _ _
  calc n * (n - 1) * (n - 2) ≤ n * n * (n - 2) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
    _ ≤ n * n * n := Nat.mul_le_mul_left _ h2
