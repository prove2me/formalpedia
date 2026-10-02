-- Prove2me | solution 1 for ProofsInTheBook.Chapter15.NoObtuseAngles.hasAntipodalStrips
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T15:41:28.723543+00:00
-- url     : https://prove2.me/submissions/a1c55c07-a126-48fe-ab8d-2654c4c4b9d9

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter15


/-!
# Chapter 15: Every large point set has an obtuse angle

The book statement is the Danzer-Grünbaum theorem: any set of more than `2^d`
points in `ℝ^d` contains three points forming an obtuse angle.

Intended Lean theorem: for `points : Finset (EuclideanSpace ℝ (Fin d))`,
`2^d < points.card` should imply that three points of `points` make an obtuse
angle, expressed by a negative inner product.

Formalization status (playbook point 17): status ①. The reduction from the
no-obtuse-angle condition to the antipodal/supporting-strip condition is
formalized below. The Klee packing geometry is formalized through the
half-sized convex-hull copies: they lie inside the original convex hull, have
volume `2^{-d}` times the hull volume, and are pairwise a.e.-disjoint. The
zero ambient-volume case is discharged by reducing to the affine span of the
point set and reapplying the same antipodal bound in that smaller Euclidean
space.

This file intentionally does not contain the old sign-vector pigeonhole theorem:
there is no assumed `sign` map and no assumed injectivity.
-/

namespace ProofsInTheBook.Chapter15

open scoped ENNReal RealInnerProductSpace
open MeasureTheory

noncomputable section











































































end

end ProofsInTheBook.Chapter15

open scoped ENNReal RealInnerProductSpace
open MeasureTheory
open ProofsInTheBook.Chapter15

theorem solution {d : ℕ} {points : Finset (Point d)}
    (hno : NoObtuseAngles points) : HasAntipodalStrips points := by
  intro a ha b hb hab x hx
  by_cases hxa : x = a
  · subst x
    rw [InPerpendicularStrip]
    constructor
    · simp
    · simp
  by_cases hxb : x = b
  · subst x
    rw [InPerpendicularStrip]
    constructor
    · simp
    · simp
  rw [InPerpendicularStrip]
  constructor
  · simpa [AngleInner] using hno b hb x hx a ha (Ne.symm hxb) (Ne.symm hab) hxa
  · simpa [AngleInner] using hno a ha x hx b hb (Ne.symm hxa) hab hxb
