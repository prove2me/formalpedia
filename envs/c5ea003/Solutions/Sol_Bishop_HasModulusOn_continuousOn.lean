-- Prove2me | solution 1 for Bishop.HasModulusOn.continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:25:15.259553+00:00
-- url     : https://prove2.me/submissions/ab797c0d-2e7e-4d9e-b6e5-937b5c34e00f

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
theorem solution{f : ℝ → ℝ} {s : Set ℝ} {ω : ℝ → ℝ}
    (hω : HasModulusOn f s ω) : ContinuousOn f s := by
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  obtain ⟨hpos, hmod⟩ := hω (ε / 2) (by linarith)
  refine ⟨ω (ε / 2), hpos, fun y hy hdist => ?_⟩
  have h1 : |x - y| ≤ ω (ε / 2) := by
    rw [abs_sub_comm]
    exact le_of_lt (by simpa [Real.dist_eq] using hdist)
  have := hmod x hx y hy h1
  have : |f y - f x| ≤ ε / 2 := by rw [abs_sub_comm]; exact this
  rw [Real.dist_eq]
  linarith
