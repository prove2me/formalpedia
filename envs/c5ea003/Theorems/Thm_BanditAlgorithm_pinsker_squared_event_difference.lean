-- Prove2me | Theorems.Thm_BanditAlgorithm_pinsker_squared_event_difference
-- name    : BanditAlgorithm.pinsker_squared_event_difference
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-19T01:55:00.357891+00:00
-- url     : https://prove2.me/theorems/18259eaf-af56-4d0c-b9d8-35be2f46b893
-- title:
--   Squared event form of Pinsker’s inequality
-- statement:
--   For probability measures $P$ and $Q$ with finite relative entropy and every measurable event $A$, the squared difference of the event probabilities satisfies $2 (Q(A)-P(A))^2 ≤ D(P‖Q)$. This is the eventwise squared form of Pinsker’s inequality; the sign convention is immaterial because the difference is squared.
-- source:
--   T. Lattimore and C. Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), Note 5, Eq. (14.12), printed p. 193 / PDF p. 202.

import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory InformationTheory Real
open scoped ENNReal

theorem BanditAlgorithm.pinsker_squared_event_difference {Ω : Type} {mΩ : MeasurableSpace Ω} (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {A : Set Ω} (hA : MeasurableSet A) (hD : klDiv P Q ≠ ∞) : 2 * (Q.real A - P.real A) ^ 2 ≤ (klDiv P Q).toReal := by sorry
