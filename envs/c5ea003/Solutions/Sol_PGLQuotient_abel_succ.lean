-- Prove2me | solution 1 for PGLQuotient.abel_succ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T09:53:04.738322+00:00
-- url     : https://prove2.me/submissions/7ab105ee-5331-49bc-bb1d-0bba234919b2

/-
# `PGLQuotient.abel_succ`
Target `8c68a06d` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle screened CLEAN. Gift: **SAFE**.

BINDERS — expected type from a WA, VERBATIM:
    ∀ {q : ℝ} {m i : ℕ}, i ≤ m → ∀ (j : ℕ), …
`q` IMPLICIT (bundle rebinds `variable {q}` at line 58, after `variable (q : ℝ)` at line 37), and
`j` comes AFTER the `i ≤ m` hypothesis. A sibling's WA on this bundle shows the other trap: an extra
`1 < q →` leaking in from `variable (hq : 1 < q)` at line 78. Neither belongs here.

VERIFIED OVER ℚ BEFORE ANY LEAN (4 values of q, full small-index range, 0 mismatches) — including
every step below, and the r = 0 boundary separately.

THE REDUCTION. Two Gpoly peels collapse this from an Abel-summation step to one scalar identity:
  * bottom peel  `Gpoly q (m+1) (i+1) = Gpoly q m i * (q^(m+1) - 1)`   <- the RHS factor IS this
  * top peel     `Gpoly q m (i+1)     = Gpoly q m i * (q^(m-i) - 1)`   <- common factor of the bracket
Cancelling `Gpoly q m i` and writing `r = m - i` (so `m + 1 = (i+1) + r`, cancelling `q^(i+1)`) leaves
    q^r * Jfac q r j = Jfac q r (j+1) - (q^r - 1) * Jfac q (r-1) (j+1)
and both sides equal `q^r * (q^(j+1) - 1) * Jfac q (r-1) (j+1)` via a bottom peel of `Jfac q r j` and
a top peel of `Jfac q r (j+1)`.

THE i = m BOUNDARY NEEDS NO SPECIAL LEMMA. There `r = 0`, and the top peel already yields
`q^(m-i) - 1 = q^0 - 1 = 0`, so the subtracted product vanishes by the SAME rewrite. `i ≤ m` permits
`i = m` rather than excluding it.

IDIOMS REUSED FROM THE SIBLING THAT PASSED PREFLIGHT (not guessed):
  * `Finset.prod_range_succ  f n : ∏ x ∈ range (n+1), f x = (∏ x ∈ range n, f x) * f n`
  * `Finset.prod_range_succ' f n : ∏ k ∈ range (n+1), f k = (∏ k ∈ range n, f (k+1)) * f 0`
    — BOTH put the peeled factor on the RIGHT.
  * `rw [Jfac]` with NO trailing `simp`: `s + 1 + 0` is definitionally `s + 1`, so `rw`'s own `rfl`
    closes it and a trailing `simp` errors with "No goals to be solved". That cost two compiles.
-/
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_VolumeAlgebra

set_option autoImplicit false
set_option maxHeartbeats 400000

open PGLQuotient Finset

open PGLQuotient in
/-- **The target, verbatim.** -/
theorem solution {q : ℝ} {m i : ℕ} (hi : i ≤ m) (j : ℕ) :
    q ^ (m + 1) * (Gpoly q (m + 1) (i + 1) * Jfac q (m + 1 - (i + 1)) j)
      = q ^ (i + 1) * (q ^ (m + 1) - 1) *
        (Gpoly q m i * Jfac q (m - i) (j + 1)
          - Gpoly q m (i + 1) * Jfac q (m - (i + 1)) (j + 1)) := by
  have hmi : m + 1 - (i + 1) = m - i := by omega
  rw [hmi]
  have hG1 : Gpoly q (m + 1) (i + 1) = Gpoly q m i * (q ^ (m + 1) - 1) := by
    rw [Gpoly, Gpoly, Finset.prod_range_succ']
    have hsub : ∀ k : ℕ, m + 1 - (k + 1) = m - k := fun k => by omega
    simp only [hsub, Nat.sub_zero]
  have hG2 : Gpoly q m (i + 1) = Gpoly q m i * (q ^ (m - i) - 1) := by
    rw [Gpoly, Gpoly, Finset.prod_range_succ]
  rw [hG1, hG2]
  rcases Nat.eq_or_lt_of_le hi with heq | hlt
  · -- i = m : the window is empty and q^(m-i) - 1 = q^0 - 1 = 0
    have h0 : m - i = 0 := by omega
    have h1 : m - (i + 1) = 0 := by omega
    have h2 : m + 1 = i + 1 := by omega
    rw [h0, h1, h2, Jfac, Jfac, Finset.prod_range_zero, Finset.prod_range_zero, pow_zero]
    ring
  · obtain ⟨r, hr⟩ : ∃ r, m - i = r + 1 := ⟨m - i - 1, by omega⟩
    have hr2 : m - (i + 1) = r := by omega
    rw [hr, hr2]
    have hJ1 : Jfac q (r + 1) j = Jfac q r (j + 1) * (q ^ (j + 1) - 1) := by
      rw [Jfac, Jfac, Finset.prod_range_succ']
      have hs : ∀ s : ℕ, s + 1 + 1 + j = s + 1 + (j + 1) := fun s => by omega
      have h0 : 0 + 1 + j = j + 1 := by omega
      simp only [hs, h0]
    have hJ2 : Jfac q (r + 1) (j + 1) = Jfac q r (j + 1) * (q ^ (r + 1 + (j + 1)) - 1) := by
      rw [Jfac, Jfac, Finset.prod_range_succ]
    rw [hJ1, hJ2]
    have e1 : q ^ (m + 1) = q ^ (i + 1) * q ^ (r + 1) := by
      rw [← pow_add]; congr 1; omega
    have e2 : q ^ (r + 1 + (j + 1)) = q ^ (r + 1) * q ^ (j + 1) := by rw [← pow_add]
    rw [e1, e2]
    ring
