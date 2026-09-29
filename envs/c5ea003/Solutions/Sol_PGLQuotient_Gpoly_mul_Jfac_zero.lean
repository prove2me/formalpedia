-- Prove2me | solution 1 for PGLQuotient.Gpoly_mul_Jfac_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T09:26:46.693361+00:00
-- url     : https://prove2.me/submissions/135e1e49-b448-4b1c-8274-8294572782a3

/-
# `PGLQuotient.Gpoly_mul_Jfac_zero`
Target `2ee63f04` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle screened CLEAN (exit 0, resolved uuid). Gift: **SAFE**.

BINDERS — THE ENTIRE WA CLUSTER. This target carries `WA,WA,WA,WA,CE`: four proofs COMPILED and were
rejected on type. The bundle rebinds its variable mid-file —
    line 37  variable (q : ℝ)    (explicit, for the definitions)
    line 58  variable {q}        (IMPLICIT, before the theorems)
— and the WA publishes the expected type verbatim: `∀ {q : ℝ} {n i : ℕ}, i ≤ n → …`. So `q` is
IMPLICIT. `c4710d1a Jfac_zero_right`, the one sibling that went ACCEPTED after the same four WAs,
has the same shape. Declaring `(q : ℝ)` compiles perfectly and fails the gate.

DEFINITIONS (read from the bundle):
    Gpoly q n i = ∏ k ∈ range i, (q^(n-k) - 1)      -- exponents n, n-1, …, n-i+1  (DESCENDING)
    Jfac  q r j = ∏ s ∈ range r, (q^(s+1+j) - 1)
    Pfac  q n   = ∏ k ∈ range n, (q^(k+1) - 1)      -- exponents 1, 2, …, n

MATHS. `Jfac q (n-i) 0` supplies exponents `1 … n-i`; `Gpoly q n i` supplies `n-i+1 … n` but in the
OPPOSITE ORDER. So: split `range n` at `n-i`, then REFLECT the second block.
`i ≤ n` is load-bearing — without it `n - i` underflows in ℕ and the split is false.

PROBED, NOT GUESSED (statements read from source, not recalled):
  * `Finset.prod_range_add (f) (n m) : ∏ x ∈ range (n+m), f x
       = (∏ x ∈ range n, f x) * ∏ x ∈ range m, f (n+x)`     — Group/Finset/Basic.lean:549
  * `Finset.prod_range_reflect (f) (n) : ∏ j ∈ range n, f (n-1-j) = ∏ j ∈ range n, f j`
                                                             — Intervals.lean:155
  * Mathlib has NO `qPochhammer` / `gaussBinomial` — grep returned nothing — so there is no ready
    q-product theory to lean on; the direct split is the route.
  * `conv_lhs` is used for the `n = (n-i)+i` rewrite: a bare `rw` would also rewrite the `n` inside
    `n - i` and loop. `exact` then closes it, unifying the beta-redex `Finset.prod_range_add` leaves.
-/
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_VolumeAlgebra

set_option autoImplicit false
set_option maxHeartbeats 400000

open PGLQuotient Finset

open PGLQuotient in
/-- **The target, verbatim.** -/
theorem solution {q : ℝ} {n i : ℕ} (hi : i ≤ n) :
    Gpoly q n i * Jfac q (n - i) 0 = Pfac q n := by
  -- split the full product at n - i
  have hadd : (∏ x ∈ Finset.range n, (q ^ (x + 1) - 1))
      = (∏ x ∈ Finset.range (n - i), (q ^ (x + 1) - 1))
        * ∏ x ∈ Finset.range i, (q ^ ((n - i) + x + 1) - 1) := by
    conv_lhs => rw [show n = (n - i) + i from by omega]
    exact Finset.prod_range_add (fun k => q ^ (k + 1) - 1) (n - i) i
  -- the bottom block IS Jfac … 0  (s + 1 + 0 = s + 1)
  have hJ : Jfac q (n - i) 0 = ∏ x ∈ Finset.range (n - i), (q ^ (x + 1) - 1) := by
    rw [Jfac]
  -- the top block is Gpoly, REFLECTED
  have hrefl : (∏ x ∈ Finset.range i, (q ^ ((n - i) + x + 1) - 1)) = Gpoly q n i := by
    rw [Gpoly, ← Finset.prod_range_reflect (fun x => q ^ (n - x) - 1) i]
    refine Finset.prod_congr rfl ?_
    intro x hx
    have hxi : x < i := Finset.mem_range.mp hx
    have hexp : (n - i) + x + 1 = n - (i - 1 - x) := by omega
    rw [hexp]
  rw [hJ, ← hrefl, Pfac, hadd]
  ring
