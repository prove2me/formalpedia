-- Prove2me | solution 1 for RademacherComparison.vc_bound_eventually_worse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:01:25.073809+00:00
-- url     : https://prove2.me/submissions/5fedf828-c879-43b8-89e8-9fe50678c734

-- Sol generated from Logic/Rademacher/Comparison.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Comparison
/-
# Rademacher complexity beats cardinality (VC) counting on structured classes

Massart's finite class lemma bounds the Rademacher complexity of a class of `N` vectors
by `r √(2 log N)/n`, and VC-type bounds bound `N` (the number of behaviours on the
sample) by a function of the VC dimension.  Both are *counting* bounds and become
vacuous for classes that are infinite on the sample.

This file computes the empirical Rademacher complexity of the Euclidean ball of
radius `r`, i.e. of the class of all vectors of length at most `r`:

  `rad (ball r) = r / √n`   (`rad_ball`),

and shows that this class is infinite (`ball_infinite`), so no cardinality bound
applies to it, while its Rademacher complexity is finite, dimension free, and even
*exactly* computable.  Every subclass of the ball inherits the bound
(`rad_le_of_subset_ball`), which is the abstract form of the margin bound for linear
predictors.

Finally `vc_bound_eventually_worse` records the quantitative comparison: for a class of
linear predictors in dimension `d`, the VC dimension grows with `d`, so any bound of the
shape `c √(d/n)` eventually exceeds the dimension-free Rademacher bound `W B / √n`.

This file is self-contained.
-/

open RademacherComparison

open Finset

variable {n : ℕ}













open RademacherComparison in
theorem solution{W B c : ℝ} (hW : 0 < W) (hB : 0 < B) (hc : 0 < c)
    (hn : 0 < n) {d : ℕ} (hd : (W * B / c) ^ 2 < d) :
    W * B / Real.sqrt n < c * Real.sqrt ((d : ℝ) / n) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hsqrt : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hdpos : (0:ℝ) < d := lt_of_le_of_lt (by positivity) hd
  have hsplit : Real.sqrt ((d : ℝ) / n) = Real.sqrt d / Real.sqrt n :=
    Real.sqrt_div hdpos.le n
  have hkey : W * B / c < Real.sqrt d := by
    have h1 : Real.sqrt ((W * B / c) ^ 2) < Real.sqrt d := by
      exact Real.sqrt_lt_sqrt (by positivity) hd
    rwa [Real.sqrt_sq (by positivity)] at h1
  rw [hsplit, div_lt_iff₀ hsqrt]
  have : c * (Real.sqrt d / Real.sqrt n) * Real.sqrt n = c * Real.sqrt d := by
    field_simp
  rw [this]
  calc W * B = c * (W * B / c) := by field_simp
    _ < c * Real.sqrt d := by exact mul_lt_mul_of_pos_left hkey hc
