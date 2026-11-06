-- Prove2me | Theorems.Thm_levy_foundations_projectiveFamily_content_tendsto_zero
-- name    : levy_foundations_projectiveFamily_content_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:16:29.830251+00:00
-- url     : https://prove2.me/theorems/8be3deca-5098-4646-be6d-861c5db9cebc
-- title:
--   Projective cylinder content is continuous from above at the empty set
-- statement:
--   For a projectively consistent family of probability measures on Polish coordinate spaces carrying their Borel σ-algebras, the corresponding cylinder content tends to zero along any decreasing sequence of measurable cylinders whose intersection is empty. This is the inner-regularity/compactness step of the Kolmogorov extension proof.
-- source:
--   Shmuel Link, LeanLevy, frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Processes/Kolmogorov.lean: https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Kolmogorov.lean (`content_tendsto_zero`).

import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Polish
import Definitions.Def_levy_foundations_projectiveFamily

open MeasureTheory Filter Set

theorem levy_foundations_projectiveFamily_content_tendsto_zero
  {ι : Type*} {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]
  [∀ i, TopologicalSpace (α i)]
  [∀ i, PolishSpace (α i)]
  [∀ i, BorelSpace (α i)]
  (pf : LevyFoundations.ProjectiveFamily ι α)
  {B : ℕ → Set (∀ i, α i)}
  (hB : ∀ n, B n ∈ measurableCylinders α)
  (hB_anti : Antitone B) (hB_inter : ⋂ n, B n = ∅) :
  Tendsto (fun n => projectiveFamilyContent pf.consistent (B n))
    atTop (nhds 0) := by sorry
