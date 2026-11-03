-- Prove2me | Theorems.Thm_levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint
-- name    : levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:06:42.023229+00:00
-- url     : https://prove2.me/theorems/666d880d-7a1c-4910-80a0-c17523c9f6a6
-- title:
--   Grouping independent random variables into disjoint blocks preserves independence
-- statement:
--   Grouping independent random variables into disjoint blocks preserves independence.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/IndependenceGrouping.lean#L134

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.PiSystem

open MeasureTheory MeasurableSpace Set ProbabilityTheory

theorem levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint
    {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {β : κ → Type*} {mβ : ∀ k, MeasurableSpace (β k)}
    {f : ∀ k, Ω → β k} (hf : ∀ k, Measurable (f k))
    (h_indep : iIndepFun f μ) {S : ι → Set κ}
    (hS : Pairwise (Function.onFun Disjoint S)) :
    iIndepFun (fun i ω => (S i).restrict fun k => f k ω) μ := by sorry
