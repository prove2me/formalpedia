-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_BezoutPluckerJets_bezoutPluckerEquiv_apply
-- name    : ErdosProblems.Erdos1049.BezoutPluckerJets.bezoutPluckerEquiv_apply
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:04:46.162998+00:00
-- url     : https://prove2.me/theorems/ed71b7ab-7012-4197-a3a5-f9541b8ba23e
-- title:
--   Bezout plucker equiv apply
-- statement:
--   For a Bézout identity ua+vb=1, the coordinate equivalence sends (x,y) to (ux+vy,ay−bx).
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/BezoutPluckerJets.lean#L78-L79
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosProblems
open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.BezoutPluckerJets
variable {R : Type*} [CommRing R]

open ErdosProblems.Erdos1049.BezoutPluckerJets

@[simp] theorem ErdosProblems.Erdos1049.BezoutPluckerJets.bezoutPluckerEquiv_apply (a b u v : R) (h : u * a + v * b = 1) (x y : R) :
    bezoutPluckerEquiv a b u v h (x, y) = (u * x + v * y, a * y - b * x) := by sorry
