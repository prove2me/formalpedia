-- Prove2me | Theorems.Thm_Erdos180_symplecticLine_eq_coordinateCenterLine_of_common_points
-- name    : Erdos180.symplecticLine_eq_coordinateCenterLine_of_common_points
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:17:40.48283+00:00
-- url     : https://prove2.me/theorems/7012fb39-ac85-42c3-aabc-7f290492c4bf
-- title:
--   Lines meeting both coordinate lines are coordinate centres
-- statement:
--   If a line $C$ meets the horizontal line in a point and the vertical line in a point, then
--   $C$ is the coordinate centre line of some direction $(x,y) \ne (0,0)$.
--
--   The complementary case of the previous classification: a line either is a graph over the
--   horizontal plane or joins the two coordinate lines. The common centres of a pair of bases in a
--   $J$-pattern are of the latter kind, which is why they are parametrised by a single projective
--   direction.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L7699-L7796

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.symplecticLine_eq_coordinateCenterLine_of_common_points
    (C : SymplecticLine K)
    (p q : SymplecticPoint K)
    (hpH : p.1 ≤ (symmetricGraphLine K 0 0 0).1)
    (hpC : p.1 ≤ C.1)
    (hqV : q.1 ≤ (symplecticVerticalLine K).1)
    (hqC : q.1 ≤ C.1) :
    ∃ (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0),
      C = coordinateCenterLine K x y hxy := by sorry
