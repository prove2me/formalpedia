-- Prove2me | Theorems.Thm_Thurston23_thurston_question_23
-- name    : Thurston23.thurston_question_23
-- status  : Open
-- author  : @t4v1
-- created : 2026-09-05T22:58:49.937456+00:00
-- url     : https://prove2.me/theorems/54aa50ff-7c96-45c8-a8be-619c7e0fb00c
-- title:
--   Goal - the volumes of hyperbolic 3-manifolds are not all rationally related
-- statement:
--   There are two hyperbolic 3-manifolds whose volumes have irrational ratio. Read literally, 'the volumes are rationally independent' is false, since a degree n cover has n times the volume; the open question is whether every rational relation arises that way. No such pair is known: for arithmetic examples Humbert's formula makes the ratio a ratio of Dedekind zeta values at 2, and separating those is a transcendence statement of the difficulty of the irrationality of zeta(5).
-- source:
--   W. P. Thurston, Bull. Amer. Math. Soc. 6 (1982), 357-381, Question 23.

import Definitions.Def_Thurston23_bundle

namespace Thurston23

open MeasureTheory

/-- **Thurston's Question 23.** The volumes of hyperbolic `3`-manifolds are not
all rationally related: some two of them have irrational ratio.

Read literally, "the volumes are rationally independent" is false, since a
degree `n` cover has `n` times the volume (Milestone 1); the open question is
whether every rational relation arises that way. It is not known how to exhibit
a single pair of hyperbolic `3`-manifolds whose volumes have irrational ratio.
For arithmetic examples Humbert's formula expresses the volume of the Bianchi
quotient of an imaginary quadratic field `F` as `|δ_F|^{3/2} ζ_F(2) / 4π²`, so
the question reduces to the irrationality of a ratio of Dedekind zeta values at
`2`, a transcendence statement of the same difficulty as the irrationality of
`ζ(5)`. -/
theorem thurston_question_23 :
    ∃ v ∈ hyperbolicVolumes, ∃ w ∈ hyperbolicVolumes,
      ∀ q : ℚ, v ≠ (q : ℝ) * w := by
  sorry

end Thurston23
