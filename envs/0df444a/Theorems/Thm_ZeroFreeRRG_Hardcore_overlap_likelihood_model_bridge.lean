-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_likelihood_model_bridge
-- name    : ZeroFreeRRG.Hardcore.overlap_likelihood_model_bridge
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T09:42:55.033076+00:00
-- url     : https://prove2.me/theorems/d9b0d46f-8cc5-482c-97bc-8ce33b9c7104
-- title:
--   Small planted log-likelihood mean from the Bethe variational estimate
-- statement:
--   For the paper’s planted configuration model, assume Condition 1 and the explicitly stated compactness, continuity, and base-point identities for the cavity-law domain, Bethe functional, and perturbation. Then for every $\varepsilon>0$ there is a reveal probability $s\in(0,1)$ such that the planted expected log-likelihood divided by $n$ is at most $\varepsilon s$ for all sufficiently large admissible $n$. This is the first step of the exponential overlap proof, conditional on those analytic properties.
-- source:
--   Conditional source-specific step in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6 and equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.overlap_likelihood_model_bridge (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t)
    (hC1 : Condition1 m d t)
    (hcompact : IsCompact (cavityLaws m t))
    (hdirac : diracPi m t ∈ cavityLaws m t)
    (hbethe : ContinuousOn (betheK m t d) (cavityLaws m t))
    (hbase : betheK m t d (diracPi m t) = 0)
    (hpert : ContinuousOn (fun ν : ProbabilityMeasure (m.Spin → ℝ) =>
      (d:ℝ) * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1)^2)
        ∂(ν : Measure (m.Spin → ℝ))) (cavityLaws m t))
    (hpertzero : (d:ℝ) * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1)^2)
      ∂((diracPi m t : ProbabilityMeasure (m.Spin → ℝ)) : Measure (m.Spin → ℝ)) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∃ N : ℕ,
      ∀ n ≥ N, Even (n*d) →
        (1:ℝ)/n * plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) ≤ ε*s := by sorry
