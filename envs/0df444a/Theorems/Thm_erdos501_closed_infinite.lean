-- Prove2me | Theorems.Thm_erdos501_closed_infinite
-- name    : erdos501_closed_infinite
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T23:16:23.386932+00:00
-- url     : https://prove2.me/theorems/bf29f409-2536-442e-a989-3dfb297a91f1
-- title:
--   Erdős 501, closed case: infinite independent set (NPS 1987)
-- statement:
--   Let $(A_x)_{x \in \mathbb{R}}$ be a family of subsets of the real line such that every $A_x$ is **closed** and has Lebesgue measure $< 1$. Then there exists an **infinite independent set**: an infinite $X \subseteq \mathbb{R}$ such that $x \notin A_y$ whenever $x, y \in X$ are distinct:
--   $$\big(\forall x,\ A_x \text{ closed}\big) \wedge \big(\forall x,\ \lambda(A_x) < 1\big) \implies \exists X \subseteq \mathbb{R} \text{ infinite},\ \forall x \neq y \in X,\ x \notin A_y.$$
--   This is the strong form of the second question of Erdős Problem 501, due to Newelski–Pawlikowski–Seredyński (1987). No boundedness hypothesis is needed.
--
--   **Formalization Note.** `volume (A x)` is the Lebesgue measure of the (closed, hence measurable) set $A_x$; independence is `X.Pairwise (fun x y => x ∉ A y)`.
-- source:
--   https://github.com/elliotglazer/erdos501/blob/218d1c1e46f77d4db80e566d1721782e85b94a17/Challenge.lean#L554-L562 (target 1); L. Newelski, J. Pawlikowski, W. Seredyński, Infinite free set for small measure set mappings, Proc. AMS 100 (1987) 335–339, https://doi.org/10.1090/S0002-9939-1987-0884475-3

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Satisfiability
import Mathlib.SetTheory.ZFC.Basic
import Definitions.Def_definable_saturated_fol
import Definitions.Def_erdos501_sentence
import Definitions.Def_erdos501_zfset_structure

open MeasureTheory
open scoped Cardinal FirstOrder
open FirstOrder FirstOrder.Language
open Erdos501.FOL

universe u

theorem erdos501_closed_infinite :
    ∀ (A : ℝ → Set ℝ),
      (∀ x, IsClosed (A x)) →
      (∀ x, volume (A x) < 1) →
      ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) := by sorry
