-- Prove2me | Theorems.Thm_levy_foundations_iIndepSets_piiUnionInter_pairwiseDisjoint
-- name    : levy_foundations_iIndepSets_piiUnionInter_pairwiseDisjoint
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:06:26.520078+00:00
-- url     : https://prove2.me/theorems/9b7c92ad-bab9-48b8-8b68-4bf82139626b
-- title:
--   Grouping pairwise-disjoint independent π-systems preserves mutual independence
-- statement:
--   Grouping pairwise-disjoint independent π-systems preserves mutual independence.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/IndependenceGrouping.lean#L40

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.PiSystem

open MeasureTheory MeasurableSpace Set ProbabilityTheory

theorem levy_foundations_iIndepSets_piiUnionInter_pairwiseDisjoint
    {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {π : κ → Set (Set Ω)} {S : ι → Set κ}
    (h_indep : iIndepSets π μ)
    (hS : Pairwise (Function.onFun Disjoint S)) :
    iIndepSets (fun i => piiUnionInter π (S i)) μ := by sorry
