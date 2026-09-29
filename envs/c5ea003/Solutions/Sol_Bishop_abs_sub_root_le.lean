-- Prove2me | solution 1 for Bishop.abs_sub_root_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:30:19.593382+00:00
-- url     : https://prove2.me/submissions/c37c7467-956f-40f2-ae7e-dee5c9f7fa09

-- Sol generated from Logic/ConstructiveAnalysis/ConstructiveIVT.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveIVT
/-
# The constructive intermediate value theorem, with explicit modulus

In Bishop's constructive analysis the classical intermediate value theorem is not
available: from `f a ≤ 0 ≤ f b` one cannot compute a point where `f` vanishes
(see `Logic/ConstructiveAnalysis/BrouwerianCounterexamples.lean`).  What *is*
constructively valid, and what Bishop proves, are:

1. the **approximate intermediate value theorem**: for every `ε > 0` one can
   *compute* a point `x ∈ [a,b]` with `|f x| ≤ ε`, provided `f` comes with a
   modulus of uniform continuity `ω`;
2. the **exact intermediate value theorem** for functions that are, in an explicit
   quantitative sense, non-constant (here: with a positive lower slope bound `c`),
   together with an explicit modulus for the root.

Both are proved below.  The approximate root is produced by an entirely explicit
finite search on the grid `a + k(b-a)/N`, `0 ≤ k ≤ N`, where `N` is any integer with
`(b-a)/N ≤ ω ε`; the witness is the *largest* grid index at which `f` is `≤ 0`.

The final theorem `exists_reg_root` presents the root of such a function as a
Bishop real (a regular sequence of rationals) whose rational approximations are
explicitly grid points of the above finite search.
-/


open Bishop

open Set










/-! ## Exact roots under an explicit non-degeneracy assumption -/






/-! ## The root as a Bishop real

Finally we present the root itself as a Bishop real: a regular sequence of
*rationals*, each term of which is one of the explicitly searched grid points. -/





open Bishop in
theorem solution{f : ℝ → ℝ} {a b c ε : ℝ} (hc : 0 < c)
    (hslope : HasSlopeBoundOn f (Icc a b) c)
    {r x : ℝ} (hr : r ∈ Icc a b) (hfr : f r = 0) (hx : x ∈ Icc a b) (hfx : |f x| ≤ ε) :
    |x - r| ≤ ε / c := by
  have hb := abs_le.mp hfx
  rcases le_total r x with h | h
  · have := hslope r hr x hx h
    rw [hfr] at this
    have : c * (x - r) ≤ ε := by linarith [hb.2]
    rw [abs_of_nonneg (by linarith), le_div_iff₀ hc]
    linarith
  · have := hslope x hx r hr h
    rw [hfr] at this
    have : c * (r - x) ≤ ε := by linarith [hb.1]
    rw [abs_of_nonpos (by linarith), le_div_iff₀ hc]
    linarith
