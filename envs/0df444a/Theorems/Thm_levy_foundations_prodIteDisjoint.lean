-- Prove2me | Theorems.Thm_levy_foundations_prodIteDisjoint
-- name    : levy_foundations_prodIteDisjoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:52:20.018476+00:00
-- url     : https://prove2.me/theorems/bbcd686e-1e31-4a95-b483-e1dbf8341ade
-- title:
--   Product of indicator factors on disjoint sets equals a sum
-- statement:
--   At any point x, at most one of the pairwise-disjoint sets A(i) contains x. Thus at most one factor of the product differs from one, and the product equals one plus the sum of the supported deviations. This is the algebraic core of the finite Poisson count-vector generating function.
-- source:
--   Independently formulated from Shmuel Link's MIT-licensed LeanLevy, PoissonPointFamily.lean, lemma prod_ite_eq_one_add_sum_indicator, source commit 7e73fd9b23ad52956ec2756a815889a783131ce4.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Notation.Indicator

open Finset Set
open Classical in

theorem levy_foundations_prodIteDisjoint
    {E ι : Type*} [Fintype ι]
    (A : ι → Set E) (hdisj : Pairwise (Function.onFun Disjoint A))
    (z : ι → ℂ) (x : E) :
    (∏ i, (if x ∈ A i then z i else 1)) =
      1 + ∑ i, (A i).indicator (fun _ => z i - 1) x := by sorry
