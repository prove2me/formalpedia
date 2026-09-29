-- Prove2me | Theorems.Thm_BanditAlgorithm_bretagnolle_huber_inequality_finite_typeStar
-- name    : BanditAlgorithm.bretagnolle_huber_inequality_finite_typeStar
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T19:37:47.133871+00:00
-- url     : https://prove2.me/theorems/a6e41790-a6e1-4e6d-9ea8-088d41700478
-- title:
--   Bretagnolle–Huber inequality on a finite type in any universe
-- statement:
--   Let $P$ and $Q$ be probability measures on a finite measurable space $(\Omega,\mathcal F)$, where the carrier type may live in any Lean universe. For every measurable event $A\in\mathcal F$, if $D(P\|Q)<\infty$, then
--
--   $$
--   \frac12\exp\!\bigl(-D(P\|Q)\bigr)
--   \le
--   P(A)+Q(A^{\mathrm c}).
--   $$
--
--   This is the Bretagnolle–Huber testing inequality. The universe-polymorphic finite-space form is useful for finite histories whose signal type is declared in an arbitrary universe.
--
--   **Formalization Note** This has the same mathematical conclusion as the existing platform theorem `BanditAlgorithm.bretagnolle_huber_inequality`; it adds a finite-carrier hypothesis so that an arbitrary-universe carrier can be measurably reindexed by a universe-zero type and the existing theorem reused.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), Theorem 14.2, printed pp. 190–191. This is a universe-polymorphic finite-space restatement of the existing platform formalization.

import Theorems.Thm_BanditAlgorithm_bretagnolle_huber_inequality
import Theorems.Thm_InformationTheory_klDiv_map_measurableEmbedding
import Mathlib.Data.Fintype.EquivFin

open MeasureTheory InformationTheory Real
open scoped ENNReal

theorem BanditAlgorithm.bretagnolle_huber_inequality_finite_typeStar
    {Ω : Type*} [Fintype Ω] {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set Ω} (hA : MeasurableSet A) (hD : klDiv P Q ≠ ∞) :
    2⁻¹ * exp (-(klDiv P Q).toReal) ≤ P.real A + Q.real Aᶜ := by
  sorry
