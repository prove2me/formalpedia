-- Prove2me | Theorems.Thm_levy_foundations_prodIteConstCard
-- name    : levy_foundations_prodIteConstCard
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:53:40.335452+00:00
-- url     : https://prove2.me/theorems/db7c0ef5-87b6-41db-bb4a-7f7c12b968a1
-- title:
--   Finite product of indicator-selected constants as a power
-- statement:
--   A finite product whose ith factor is z when p(i) and one otherwise equals z raised to the number of indices satisfying p. Provides the pointwise product identity for thinned Poisson counts.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), PoissonPointFamily.lean, frozen source commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Awaiting private remote Lean verification.

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Complex.Basic

open Finset

theorem levy_foundations_prodIteConstCard
    {ι : Type*} (s : Finset ι) (p : ι → Prop)
    [DecidablePred p] (z : ℂ) :
    ∏ i ∈ s, (if p i then z else 1) = z ^ (s.filter p).card := by sorry
