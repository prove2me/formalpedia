-- Prove2me | solution 1 for BookSixth.disk_cut_difference_affine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T02:49:42.390243+00:00
-- url     : https://prove2.me/submissions/aac28f93-4557-4138-9f2f-ecb4e4b3385a

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

/-- **The difference of two flat-disk cut functions along a line is affine.**

For a Euclidean unit direction `e` and a point `a` on the line, let

    fᵢ(s) = rᵢ² − ‖a + s·e − cᵢ‖₂²

be the height of the lifted spherical dome over the flat disk with centre `cᵢ` and
radius `rᵢ`, evaluated at the point of the line with parameter `s`. The quadratic
term carries the coefficient `−∑ i, e i * e i`, which does not depend on the disk,
so it cancels in `f₁(s) − f₂(s)` and the difference is affine in `s`.

The hypothesis `(∑ i, e i * e i) = 1` records that `e` is a Euclidean unit vector
rather than a supremum-norm unit vector — the distinction that matters throughout,
since `Space3` carries the supremum norm while the dome equations use the Euclidean
one. The identity itself holds without it, so the hypothesis is not needed for the
expansion. -/
theorem solution (a e c₁ c₂ : Space3) (r₁ r₂ : ℝ) (he : (∑ i, e i * e i) = 1)
    (s : ℝ) :
    (r₁ ^ 2 - (∑ i, (a i + s * e i - c₁ i) * (a i + s * e i - c₁ i)))
      - (r₂ ^ 2 - (∑ i, (a i + s * e i - c₂ i) * (a i + s * e i - c₂ i)))
    = (r₁ ^ 2 - r₂ ^ 2) - (∑ i, (a i - c₁ i) * (a i - c₁ i))
      + (∑ i, (a i - c₂ i) * (a i - c₂ i))
      - 2 * s * ((∑ i, e i * (a i - c₁ i)) - (∑ i, e i * (a i - c₂ i))) := by
  -- `Fin.sum_univ_three` rewrites each `∑ i : Fin 3` as an explicit sum of its three
  -- summands `f 0 + f 1 + f 2`, so the whole goal becomes a polynomial identity in
  -- the three real coordinates. No `Finset` rewriting is used: `ring` cannot see
  -- through a `Finset.sum`, but it closes the expanded goal outright, which is why
  -- the `s ^ 2 * (∑ i, e i * e i)` term cancels between the two disks.
  simp only [Fin.sum_univ_three]
  ring
