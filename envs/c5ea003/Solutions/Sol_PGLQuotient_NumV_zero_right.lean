-- Prove2me | solution 1 for PGLQuotient.NumV_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T09:30:23.708329+00:00
-- url     : https://prove2.me/submissions/67240762-fb42-4290-be79-2f75b883076d

/-
# `PGLQuotient.NumV_zero_right`
Target `420826b4` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle screened CLEAN (exit 0, resolved uuid). Gift: **SAFE**.

BINDERS — expected type from the WA, VERBATIM (this target carries `WA,WA,WA,WA,CE`):
    ∀ {q : ℝ} (n c : ℕ), NumV q n c 0 = Pfac q n * ∑ i ∈ Finset.range (n + 1), q ^ (c * i)
`q` is IMPLICIT — the bundle declares `variable (q : ℝ)` at line 37 for its definitions and REBINDS
it as `variable {q}` at line 58, before the theorems. `n` and `c` are explicit. Declaring `(q : ℝ)`
compiles perfectly and fails the type-match gate; that is the entire WA cluster on this bundle.

DEFINITION (read from the bundle, line 52):
    NumV q n c j = ∑ i ∈ range (n+1), q^(c*i) * (Gpoly q n i * Jfac q (n-i) j)

MATHS. At `j = 0` every inner product collapses. The index runs over `range (n+1)`, so every `i`
satisfies `i ≤ n` — exactly the hypothesis the collapse needs — and
    Gpoly q n i * Jfac q (n-i) 0 = Pfac q n
independently of `i`. The sum therefore has a constant factor, which comes out:
    ∑ i, q^(c*i) * Pfac q n = Pfac q n * ∑ i, q^(c*i)

`i ≤ n` is where `range (n+1)` rather than `range n` matters: `Nat.lt_succ_iff` turns membership into
the needed inequality. With `range n` the top term would be missing and the identity would be false.

The collapse lemma is `2ee63f04 Gpoly_mul_Jfac_zero`, which I have submitted separately. It is
RE-DERIVED INLINE here: importing it from `Theorems/` would make this depend on that tree
transitively and force the reduction path with an axiom audit.

PROBED, NOT GUESSED — statements read from Mathlib source, not recalled:
  * `Finset.prod_range_add (f) (n m) : ∏ x ∈ range (n+m), f x
       = (∏ x ∈ range n, f x) * ∏ x ∈ range m, f (n+x)`   — Group/Finset/Basic.lean:549
  * `Finset.prod_range_reflect (f) (n) : ∏ j ∈ range n, f (n-1-j) = ∏ j ∈ range n, f j`
                                                           — Intervals.lean:155
  * `conv_lhs` for the `n = (n-i)+i` rewrite — a bare `rw` also rewrites the `n` inside `n - i`.
-/
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_VolumeAlgebra

set_option autoImplicit false
set_option maxHeartbeats 400000

open PGLQuotient Finset

open PGLQuotient in
/-- **The target, verbatim.** -/
theorem solution {q : ℝ} (n c : ℕ) :
    NumV q n c 0 = Pfac q n * ∑ i ∈ Finset.range (n + 1), q ^ (c * i) := by
  -- the collapse lemma, re-derived inline (see header)
  have key : ∀ (m j : ℕ), j ≤ m → Gpoly q m j * Jfac q (m - j) 0 = Pfac q m := by
    intro m j hj
    have hadd : (∏ x ∈ Finset.range m, (q ^ (x + 1) - 1))
        = (∏ x ∈ Finset.range (m - j), (q ^ (x + 1) - 1))
          * ∏ x ∈ Finset.range j, (q ^ ((m - j) + x + 1) - 1) := by
      conv_lhs => rw [show m = (m - j) + j from by omega]
      exact Finset.prod_range_add (fun k => q ^ (k + 1) - 1) (m - j) j
    have hJ : Jfac q (m - j) 0 = ∏ x ∈ Finset.range (m - j), (q ^ (x + 1) - 1) := by
      rw [Jfac]
    have hrefl : (∏ x ∈ Finset.range j, (q ^ ((m - j) + x + 1) - 1)) = Gpoly q m j := by
      rw [Gpoly, ← Finset.prod_range_reflect (fun x => q ^ (m - x) - 1) j]
      refine Finset.prod_congr rfl ?_
      intro x hx
      have hxj : x < j := Finset.mem_range.mp hx
      have hexp : (m - j) + x + 1 = m - (j - 1 - x) := by omega
      rw [hexp]
    rw [hJ, ← hrefl, Pfac, hadd]
    ring
  rw [NumV, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [key n i hin]
  ring
