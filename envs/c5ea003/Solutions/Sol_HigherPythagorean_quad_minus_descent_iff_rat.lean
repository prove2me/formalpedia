-- Prove2me | solution 1 for HigherPythagorean.quad_minus_descent_iff_rat
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:06:42.082025+00:00
-- url     : https://prove2.me/submissions/d2971853-f366-40d5-a5bc-a162e6d44b38

-- Sol generated from Shared/HigherPythagorean/HarmonicLaw.lean
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_BranchingContrast
import Definitions.Def_Shared_HigherPythagorean_LorentzCore
import Definitions.Def_Shared_HigherPythagorean_QuadrupleTree
import Definitions.Def_Shared_Ispythquadruple_IsPythQuadruple

/-!
# The harmonic branching law for Pythagorean quadruples

`BranchingContrast` shows that a Pythagorean quadruple has at most two parents.  Here we
determine *exactly when* the second parent exists, and the answer is an Egyptian-fraction
("harmonic") law:

> the reflection move with a minus sign on the coordinate `a` descends **iff** `1/a > 1/b + 1/c`.

This is the dimension-three replacement for the (empty) second-parent condition of the Berggren
tree, and it explains all the phenomena observed in dimension three:

* `quad_minus_descent_iff` / `quad_minus_descent_iff_rat` : the law, in integral and harmonic form.
* `harmonic_law_at_most_one_index` : the harmonic inequality can hold for at most one coordinate
  (a two-line proof of the "at most two parents" bound).
* `quad_neutral_move_iff` : the boundary case `1/a = 1/b + 1/c` gives a *height preserving*
  ("horizontal") move — a phenomenon that does not exist for triples (`triple_no_neutral_move`),
  realised e.g. by the quadruple `(1,2,2,3)`.
* `quad_one_descent_family` : the family `(2m, 2m, 2m²−1, 2m²+1)` has a **unique** parent, while
  `(1, 2m, 2m², 2m²+1)` has two; hence (`quad_branching_not_constant`) the branching number of
  the quadruple graph is genuinely non-constant, taking both possible values infinitely often.
-/

open HigherPythagorean

/-! ## The harmonic law -/

/-- **Harmonic branching law (integral form).**  The move with a minus sign on the first
coordinate strictly decreases the height iff `a(b+c) < bc`. -/
theorem quad_minus_descent_iff {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : IsPythQuadruple a b c d) : Descends (-1) 1 1 a b c d ↔ a * (b + c) < b * c := by
  unfold IsPythQuadruple at h
  unfold Descends
  constructor
  · intro hdes
    nlinarith
  · intro hlaw
    have hbc : a < b + c := by nlinarith
    nlinarith



/-! ## Neutral (height preserving) moves -/




/-! ## A family with a unique parent -/







open HigherPythagorean in
theorem solution{a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (h : IsPythQuadruple a b c d) :
    Descends (-1) 1 1 a b c d ↔ (1 : ℚ) / (b : ℚ) + 1 / (c : ℚ) < 1 / (a : ℚ) := by
  rw [quad_minus_descent_iff ha hb hc hd h]
  have ha' : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
  have hb' : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have hc' : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hc
  rw [div_add_div _ _ (ne_of_gt hb') (ne_of_gt hc'), div_lt_div_iff₀ (by positivity) ha']
  constructor
  · intro hlaw
    have : ((a : ℚ)) * ((b : ℚ) + (c : ℚ)) < (b : ℚ) * (c : ℚ) := by exact_mod_cast hlaw
    nlinarith
  · intro hlaw
    have : ((a : ℚ)) * ((b : ℚ) + (c : ℚ)) < (b : ℚ) * (c : ℚ) := by nlinarith
    exact_mod_cast this
