-- Prove2me | Definitions.Def_Logic_Rademacher_Comparison
-- name    : Logic_Rademacher_Comparison
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:07:26.247132+00:00
-- url     : https://prove2.me/theorems/53d218c6-904b-48a4-9150-105078887743
-- title:
--   Aether Catalog definitions — Logic_Rademacher_Comparison
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.Rademacher.Comparison`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/Rademacher/Comparison.lean by skeleton subtraction
import Mathlib
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

namespace RademacherComparison

open Finset

variable {n : ℕ}

/-- The sign vector attached to a boolean vector: `true ↦ 1`, `false ↦ -1`. -/
def sgn (ε : Fin n → Bool) (i : Fin n) : ℝ := if ε i then 1 else -1


/-- The linear functional `v ↦ (1/n) ∑ σ i * v i` associated with a sign vector. -/
noncomputable def signAvg (ε : Fin n → Bool) (v : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, sgn ε i * v i

/-- The empirical Rademacher complexity of a class `F` of vectors. -/
noncomputable def rad (F : Set (Fin n → ℝ)) : ℝ :=
  (∑ ε : Fin n → Bool, sSup (signAvg ε '' F)) / 2 ^ n

/-- The Euclidean ball of radius `r` in the sample space `ℝⁿ`. -/
def ball (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) := {v | ∑ i, (v i) ^ 2 ≤ r ^ 2}







end RademacherComparison


