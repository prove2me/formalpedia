-- Prove2me | Theorems.Thm_ReweightedNPMLE_measureReal_prod_le_of_uniform_section_bound
-- name    : ReweightedNPMLE.measureReal_prod_le_of_uniform_section_bound
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:47:39.951389+00:00
-- url     : https://prove2.me/theorems/5b84399c-82bd-4b01-94c6-e6eda0128dbf
-- title:
--   Integrating a uniform section bound outside an exceptional set
-- statement:
--   Let $P$ and $Q$ be probability measures on measurable spaces $X$ and $Y$. Let $E\subset X\times Y$ and $D\subset X$ be measurable, and let $\varepsilon\ge0$. For $x\in X$, write $E_x=\{y:(x,y)\in E\}$. If
--   $$Q(E_x)\le\varepsilon\qquad\text{for every }x\notin D,$$
--   then
--   $$(P\otimes Q)(E)\le P(D)+\varepsilon.$$
--   The section estimates are pointwise outside $D$. They may be established using different auxiliary witnesses at different parameters; only the joint event itself needs to be measurable.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ConditionalProductBound.lean#L20-L61

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Integrating uniform conditional exceptional-event bounds

A measurable joint bad event whose sections have probability at most `eps`
off a data exceptional set has total probability at most the data failure
plus `eps`. The section bounds may come from arbitrary pointwise witnesses;
no measurable choice of those witnesses is required.
-/

open Set MeasureTheory
open scoped ENNReal

theorem ReweightedNPMLE.measureReal_prod_le_of_uniform_section_bound {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Set (X × Y)) (hE : MeasurableSet E)
    (D : Set X) (hD : MeasurableSet D) {eps : ℝ} (heps : 0 ≤ eps)
    (hsection : ∀ x ∉ D, Q.real (Prod.mk x ⁻¹' E) ≤ eps) :
    (P.prod Q).real E ≤ P.real D + eps := by sorry
