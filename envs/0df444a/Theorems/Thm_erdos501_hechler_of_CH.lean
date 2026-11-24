-- Prove2me | Theorems.Thm_erdos501_hechler_of_CH
-- name    : erdos501_hechler_of_CH
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T23:17:05.22482+00:00
-- url     : https://prove2.me/theorems/2c4dd148-a4f7-497d-82c3-b7ea2fd58f42
-- title:
--   Erdős 501: Hechler's counterexample under $\aleph_1 = \mathfrak{c}$
-- statement:
--   Assume the **continuum hypothesis**, rendered as $\aleph_1 = \mathfrak{c}$. Then there exists a family $(A_x)_{x \in \mathbb{R}}$ of **bounded** subsets of $\mathbb{R}$, each of Lebesgue **outer measure** $< 1$, with **no infinite independent set**:
--   $$\aleph_1 = \mathfrak{c} \implies \exists A,\ \big(\forall x,\ A_x \text{ bounded}\big) \wedge \big(\forall x,\ \lambda^*(A_x) < 1\big) \wedge \neg\,\exists X \text{ infinite and independent}.$$
--   This is Hechler's theorem (1972): under CH the first question of Erdős Problem 501 has a negative answer. It is a theorem of ZFC — CH is a genuine hypothesis of the theorem, not an ambient assumption. Hechler's construction in fact yields countable, null sets, a stronger property this statement does not assert.
--
--   **Formalization Note.** Boundedness is `Bornology.IsBounded`; outer measure is `volume.toOuterMeasure` (Lebesgue outer measure on an arbitrary set); CH is `(ℵ₁ : Cardinal.{u}) = 𝔠`, universe-polymorphic.
-- source:
--   https://github.com/elliotglazer/erdos501/blob/218d1c1e46f77d4db80e566d1721782e85b94a17/Challenge.lean#L576-L588 (target 3); S. H. Hechler, Directed graphs over topological spaces: some set theoretical aspects, Israel J. Math. 11 (1972) 231–248, https://doi.org/10.1007/BF02789314

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

theorem erdos501_hechler_of_CH :
    ((ℵ₁ : Cardinal.{u}) = 𝔠) →
    ∃ (A : ℝ → Set ℝ),
      (∀ x, Bornology.IsBounded (A x)) ∧
      (∀ x, volume.toOuterMeasure (A x) < 1) ∧
      ¬ ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) := by sorry
