-- Prove2me | solution 1 for HigherPythagorean.oneParent_family_isPrimQuad
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:06:41.429839+00:00
-- url     : https://prove2.me/submissions/254100d2-c148-4418-ab56-a6953557e513

-- Sol generated from Shared/HigherPythagorean/HarmonicLaw.lean
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_BranchingContrast
import Definitions.Def_Shared_HigherPythagorean_LorentzCore
import Definitions.Def_Shared_HigherPythagorean_QuadrupleTree
import Definitions.Def_Shared_Ispythquadruple_IsPythQuadruple
import Theorems.Thm_HigherPythagorean_content_dvd_fth
import Theorems.Thm_HigherPythagorean_content_dvd_thd

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




/-! ## Neutral (height preserving) moves -/




/-! ## A family with a unique parent -/







open HigherPythagorean in
theorem solution(m : ℤ) :
    IsPrimQuad (2 * m) (2 * m) (2 * m ^ 2 - 1) (2 * m ^ 2 + 1) := by
  refine ⟨by unfold IsPythQuadruple; ring, ?_⟩
  have h3 := content_dvd_thd (2 * m) (2 * m) (2 * m ^ 2 - 1) (2 * m ^ 2 + 1)
  have h4 := content_dvd_fth (2 * m) (2 * m) (2 * m ^ 2 - 1) (2 * m ^ 2 + 1)
  have h2 : ((content (2 * m) (2 * m) (2 * m ^ 2 - 1) (2 * m ^ 2 + 1) : ℕ) : ℤ) ∣ 2 := by
    have := dvd_sub h4 h3
    simpa [show 2 * m ^ 2 + 1 - (2 * m ^ 2 - 1) = 2 from by ring] using this
  have hg2 : content (2 * m) (2 * m) (2 * m ^ 2 - 1) (2 * m ^ 2 + 1) ∣ 2 := by exact_mod_cast h2
  rcases (Nat.prime_two.eq_one_or_self_of_dvd _ hg2) with h | h
  · exact h
  · exfalso
    rw [h] at h3
    omega
