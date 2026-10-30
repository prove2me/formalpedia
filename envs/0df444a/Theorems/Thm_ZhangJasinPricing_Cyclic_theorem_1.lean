-- Prove2me | Theorems.Thm_ZhangJasinPricing_Cyclic_theorem_1
-- name    : ZhangJasinPricing.Cyclic.theorem_1
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T07:01:41.73091+00:00
-- url     : https://prove2.me/theorems/22f0fcde-55f4-4098-9dc6-0638c359e049
-- title:
--   Theorem 1 — Both instance-dependent and instance-independent signed bounds for OLD and OLT
-- statement:
--   There exist positive constants Ψ₁ and Ψ₂, independent of the horizon and every model parameter, such that for every customer model satisfying Assumption 1, and every prescribed initialization and measurable maximizing tie choice for OLD and OLT, the minimum positive gaps Δᴰᵉᶜ and Δᵀᴿ over the full respective cyclic policy classes exist. For every integer T≥2,
--
--   $$R_T^{Dec}\le\frac{\Psi_1}{\Delta^{Dec}}\frac{\log T}{T},\qquad R_T^{TR}\le\frac{\Psi_1}{\Delta^{TR}}\frac{\log T}{T},$$
--   $$R_T^{Dec}\le\Psi_2\sqrt{\frac{\log T}{T}},\qquad R_T^{TR}\le\Psi_2\sqrt{\frac{\log T}{T}}.$$
--
--   Here R is expected achieved revenue divided by T minus the corresponding full-class benchmark, as printed. Revenue includes initialization, clearing, and the actual final prefix. The independent bounds are separate conjuncts for every instance; they are not conditional on an assumed gap witness.
--
--   Differences from the source:
--   - encoding: finite ordered prices, nonnegative cohort amounts, and a general probability law → zero-based natural-number indices with explicit bounds, real cohort amounts, and a measurable probability space; reason: the same instances are represented; real amounts also include the uniform demands used on p. 28
--   - reading: Definition 1 mixes a strict maximum set with a non-strict empty-set test → the maximum and fallback use the displayed strict set; reason: the printed cases leave repeated thresholds undefined; this releases a threshold once reached and retains the larger class (I4)
--   - reading: the p. 9 transition display omits the last waiting cohort → transition experiments follow equation (1), including all previous still-patient cohorts through period ℓ; reason: this is the operational definition on p. 8 and resolves the explicit indexing typo (I3)
--   - reading: Assumption 1 overloads r as a mean and a realization → the ψ₂ bound one applies to revenue realizations and centered errors have finite ψ₂ norm; reason: the text says norm of all r; the informal tail display is not a separate MGF normalization
--   - reading: initialization tests every parameter, with a suggested reset/high/drop procedure → any finite covering list of prescribed test blocks, with incidental high-price samples, reset observations retained as revenue, and a final reset; reason: this specifies the underdetermined testing and first-episode clearing conventions without favorable estimates or idle delays
--   - reading: the constants are independent of T and all other problem parameters {rᵢ} and {rᵢⱼℓ} → the same two constants precede the model, M, K, initialization, and tie rules; reason: this is the non-narrowing reading of all other problem parameters required by the brief
--   - reading: Δ is called the minimum positive gap and occurs in denominators → existence of actual least positive gaps is an explicit conclusion, with independent bounds as separate conjuncts; reason: the minimum may not exist, including on ordinary instances (I5); assuming it or replacing it by an infimum would discard source instances
--   - generalization: OLT initialization tests each parameter once (p. 20); OLD says at least once (p. 13) → OLT also permits repeated targeted tests in the finite covering list; reason: choosing each parameter once recovers the printed OLT testing prescription under the declared block/reset reading; no source instance in that prescription is excluded
--   - reading: the drop maximum in (2) includes j=i although drop parameters are defined only for j<i → the j=i case is its separately displayed r_i branch; reason: the p. 10 explanation separates equality from the strict-drop case; no undefined diagonal drop parameter is introduced
-- source:
--   Zhang and Jasin (2021), DOI 10.1287/msom.2021.0979, supplied 34-page artifact, Theorem 1, pp. 22–23 (PDF pp. 22–23)

import Definitions.Def_ZhangJasinPricing_Cyclic_Model
import Definitions.Def_ZhangJasinPricing_Cyclic_Policies
import Definitions.Def_ZhangJasinPricing_Cyclic_DynamicPrograms
import Definitions.Def_ZhangJasinPricing_Cyclic_Learning
import Definitions.Def_ZhangJasinPricing_Cyclic_Analysis
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace ZhangJasinPricing.Cyclic
theorem theorem_1 :
    ∃ Ψ₁ Ψ₂ : ℝ, 0 < Ψ₁ ∧ 0 < Ψ₂ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (D : Model Ω) (_hA : Assumption1 D),
      ∀ (initD initT : Initialization D.M D.K) (tieD tieT : TieRule),
        (∃ ΔD ΔT : ℝ, IsLeast (positiveGaps D .decreasing) ΔD ∧
          IsLeast (positiveGaps D .threshold) ΔT ∧
          ∀ T : ℕ, 2 ≤ T →
            signedRegret D .decreasing initD tieD T ≤ Ψ₁ / ΔD * Real.log T / T ∧
            signedRegret D .threshold initT tieT T ≤ Ψ₁ / ΔT * Real.log T / T) ∧
        (∀ T : ℕ, 2 ≤ T →
          signedRegret D .decreasing initD tieD T ≤ Ψ₂ * Real.sqrt (Real.log T / T) ∧
          signedRegret D .threshold initT tieT T ≤ Ψ₂ * Real.sqrt (Real.log T / T)) := by sorry
end ZhangJasinPricing.Cyclic
