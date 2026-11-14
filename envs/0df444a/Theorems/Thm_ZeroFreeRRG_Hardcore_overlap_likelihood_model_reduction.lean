-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_likelihood_model_reduction
-- name    : ZeroFreeRRG.Hardcore.overlap_likelihood_model_reduction
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T09:47:42.69254+00:00
-- url     : https://prove2.me/theorems/08571296-6cc3-459c-ab28-9276d9072eff
-- title:
--   Small planted likelihood mean under compact variational hypotheses
-- statement:
--   For the paper’s positive-parameter hardcore or Potts model, suppose Condition 1 holds, the cavity-law set is compact, and the Bethe and reveal-perturbation functionals are continuous on it. Then for every $\varepsilon>0$, some reveal probability $s\in(0,1)$ makes the planted expected pinned log-likelihood divided by $n$ at most $\varepsilon s$ for all sufficiently large admissible $n$. The explicit compactness and continuity hypotheses isolate analytic properties used in the proof of the exponential overlap lemma.
-- source:
--   Conditional source-specific reduction in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6 and equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.overlap_likelihood_model_reduction (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t)
    (hC1 : Condition1 m d t)
    (hcompact : IsCompact (cavityLaws m t))
    (hbethe : ContinuousOn (betheK m t d) (cavityLaws m t))
    (hpert : ContinuousOn (fun ν : ProbabilityMeasure (m.Spin → ℝ) =>
      (d:ℝ) * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1)^2)
        ∂(ν : Measure (m.Spin → ℝ))) (cavityLaws m t)) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∃ N : ℕ,
      ∀ n ≥ N, Even (n*d) →
        (1:ℝ)/n * plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) ≤ ε*s := by sorry
