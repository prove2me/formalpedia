-- Prove2me | Theorems.Thm_erdos501_sentence_faithful
-- name    : erdos501_sentence_faithful
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T23:18:24.72165+00:00
-- url     : https://prove2.me/theorems/d9e6bd3b-5c7f-49de-ac63-24d4ad26ea67
-- title:
--   Erdős 501: faithfulness of the first-order rendering in ZFSet
-- statement:
--   **Faithfulness of the rendering.** In Mathlib's `ZFSet`, with the standard interpretation of $\emptyset, \omega, \mathcal{P}, \bigcup, (\cdot,\cdot), \in$ (the structure `zfsetStructure`), the sentence $\varphi_{501}$ holds if and only if the Mathlib-level statement of the first question of Erdős Problem 501 holds:
--   $$\big(\mathrm{ZFSet} \models \varphi_{501}\big) \iff \Big[\forall A,\ \big(\forall x,\ A_x \text{ bounded}\big) \to \big(\forall x,\ \lambda^*(A_x) < 1\big) \to \exists X \text{ infinite and independent}\Big].$$
--   The right-hand side is verbatim the proposition `erdos_501` of `google-deepmind/formal-conjectures`. This target reduces the audit of the first-order sentence to the audit of the standard structure and of the Mathlib-level statement: a rendering that is vacuous or deviant cannot pass this equivalence.
--
--   **Formalization Note.** $\models$ is Mathlib's theory-model relation for the structure `zfsetStructure` on `ZFSet.{0}`; the right-hand side uses `Bornology.IsBounded` and `volume.toOuterMeasure`.
-- source:
--   https://github.com/elliotglazer/erdos501/blob/218d1c1e46f77d4db80e566d1721782e85b94a17/Challenge.lean#L611-L621 (target 7); google-deepmind/formal-conjectures, FormalConjectures/ErdosProblems/501.lean (erdos_501)

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

theorem erdos501_sentence_faithful :
    (ZFSet.{0} ⊨ Erdos501) ↔
      ∀ (A : ℝ → Set ℝ),
        (∀ x, Bornology.IsBounded (A x)) →
        (∀ x, volume.toOuterMeasure (A x) < 1) →
        ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) := by sorry
