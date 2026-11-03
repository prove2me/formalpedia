-- Prove2me | Theorems.Thm_levy_foundations_measurableFilterCard
-- name    : levy_foundations_measurableFilterCard
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:19:54.84298+00:00
-- url     : https://prove2.me/theorems/25121e86-dc88-40cd-8c02-f5c2de926e95
-- title:
--   Measurability of a random finite count of marked coordinates
-- statement:
--   For any measurable random natural count and measurable marked points, the number of points falling in a fixed measurable set is a measurable natural-valued random variable.
-- source:
--   Adapted from Shmuel Link's MIT-licensed LeanLevy/RandomMeasure/PoissonRandomMeasure.lean, measurable_filterCard (around line 192), commit 7e73fd9b23ad52956ec2756a815889a783131ce4.

import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory
open Classical in

theorem levy_foundations_measurableFilterCard
    {D E : Type*} [MeasurableSpace D] [MeasurableSpace E]
    (A : Set E) (hA : MeasurableSet A)
    (cnt : D → ℕ) (pt : ℕ → D → E)
    (hcnt : Measurable cnt) (hpt : ∀ n, Measurable (pt n)) :
    Measurable (fun g => ((Finset.range (cnt g)).filter
      (fun n => pt n g ∈ A)).card) := by sorry
