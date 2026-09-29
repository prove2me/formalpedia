-- Prove2me | Theorems.Thm_BanditAlgorithm_pmStochMeasure_kl_le_outside_selection
-- name    : BanditAlgorithm.pmStochMeasure_kl_le_outside_selection
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T18:24:22.840791+00:00
-- url     : https://prove2.me/theorems/501d41ba-37ec-4ffd-bcfd-ad8ae7629659
-- title:
--   Adaptive KL bound by outside-neighbourhood exploration
-- statement:
--   Consider two stochastic partial-monitoring environments $u$ and $v$, run under the same adaptive policy. Let $N$ be a finite collection of actions whose induced feedback laws agree in the two environments. Suppose every one-step feedback divergence is finite and, for every action outside $N$,
--
--   $$
--   D(P_c^u\Vert P_c^v)\le B.
--   $$
--
--   Then, at every horizon $n$, the divergence between the two adaptive feedback-history laws satisfies
--
--   $$
--   D(P_u^n\Vert P_v^n)\le B\sum_{t=0}^{n-1}\mathbb E_u\!\left[\sum_{c\notin N}\pi_t(c\mid H_t)\right].
--   $$
--
--   Thus information can accumulate only on rounds when the policy selects an action outside the feedback-indistinguishable set. This is the reusable adaptive chain-rule inequality underlying the hard partial-monitoring lower bound.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (Cambridge University Press, 2020), Chapter 37, Theorem 37.12 Step 2, p. 490, Eq. (37.8), specialized with zero feedback divergence on N_ab and a uniform one-step bound outside N_ab.

import Definitions.Def_PartialMonitoringStochastic
import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal

theorem BanditAlgorithm.pmStochMeasure_kl_le_outside_selection
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u v : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (hv : v ∈ stdSimplex ℝ (Fin d)) (N : Finset (Fin k)) (B : ℝ≥0∞)
    (hfin : ∀ c, klDiv (pmSignalMeasure G u c) (pmSignalMeasure G v c) ≠ ⊤)
    (heq : ∀ c, c ∈ N → pmSignalMeasure G u c = pmSignalMeasure G v c)
    (hle : ∀ c, c ∉ N → klDiv (pmSignalMeasure G u c) (pmSignalMeasure G v c) ≤ B) :
    ∀ n : ℕ,
      klDiv (pmStochMeasure G π u hu n) (pmStochMeasure G π v hv n) ≤
        B * ∑ t ∈ Finset.range n,
          ∫⁻ h, ∑ c ∈ Finset.univ.filter (fun c => c ∉ N),
            (π.select t h) {c} ∂pmStochMeasure G π u hu t := by
  sorry
