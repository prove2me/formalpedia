-- Prove2me | Theorems.Thm_erdos501_closed_size3
-- name    : erdos501_closed_size3
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T23:16:42.779984+00:00
-- url     : https://prove2.me/theorems/ea88698a-156d-448f-a918-1e645a126fb4
-- title:
--   Erdős 501, second question as asked: an independent set of size 3
-- statement:
--   Let $(A_x)_{x \in \mathbb{R}}$ be a family of subsets of the real line such that every $A_x$ is **closed** and has Lebesgue measure $< 1$. Then there exists an **independent set of size $3$**: a finite $X \subseteq \mathbb{R}$ with at least three elements such that $x \notin A_y$ whenever $x, y \in X$ are distinct:
--   $$\big(\forall x,\ A_x \text{ closed}\big) \wedge \big(\forall x,\ \lambda(A_x) < 1\big) \implies \exists X \subseteq \mathbb{R} \text{ finite},\ |X| \ge 3,\ \forall x \neq y \in X,\ x \notin A_y.$$
--   This is the second question of Erdős Problem 501 as originally asked (Erdős 1961; Erdős–Hajnal 1971, Problem 38); it follows from the infinite form (Target 1).
--
--   **Formalization Note.** "Size 3" is rendered as `3 ≤ X.ncard`; `Set.ncard` is $0$ on infinite sets, so the statement asserts a *finite* independent set with at least three elements.
-- source:
--   https://github.com/elliotglazer/erdos501/blob/218d1c1e46f77d4db80e566d1721782e85b94a17/Challenge.lean#L564-L572 (target 2); P. Erdős (1961), Problem II.9; P. Erdős, A. Hajnal (1971), Problem 38; https://www.erdosproblems.com/501

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

theorem erdos501_closed_size3 :
    ∀ (A : ℝ → Set ℝ),
      (∀ x, IsClosed (A x)) →
      (∀ x, volume (A x) < 1) →
      ∃ X : Set ℝ, 3 ≤ X.ncard ∧ X.Pairwise (fun x y => x ∉ A y) := by sorry
