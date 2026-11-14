-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_20_variational_limsup
-- name    : ZeroFreeRRG.Hardcore.lemma_4_20_variational_limsup
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T10:46:42.319179+00:00
-- url     : https://prove2.me/theorems/56f32dd3-e323-4727-9369-f648ba9042ab
-- title:
--   Lemma 4.20: variational bound on the planted likelihood
-- statement:
--   For every reveal rate s in [0,1], the two planted normalized log-likelihood limsups are bounded as in equation (29) by the maximum of the Bethe functional plus the stated reveal perturbation, and the maximum is attained.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 31, Lemma 4.20 and equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
open scoped Classical
open Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore

theorem ZeroFreeRRG.Hardcore.lemma_4_20_variational_limsup (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∃ ν₀ ∈ cavityLaws m t,
        (∀ ν ∈ cavityLaws m t,
          betheK m t d ν + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
              ∂(ν : Measure (m.Spin → ℝ)) ≤
          betheK m t d ν₀ + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
              ∂(ν₀ : Measure (m.Spin → ℝ))) ∧
        limsup (fun n : ℕ => (((1 : ℝ) / n *
            plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) : ℝ) : EReal))
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) ≤
          limsup (fun n : ℕ => (((1 : ℝ) / n *
            plantedPinnedE m t s d n (fun M σ U => Real.log (normZ m t M) + pinnedLL m t M σ U)
              : ℝ) : EReal))
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) ∧
        limsup (fun n : ℕ => (((1 : ℝ) / n *
            plantedPinnedE m t s d n (fun M σ U => Real.log (normZ m t M) + pinnedLL m t M σ U)
              : ℝ) : EReal))
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) ≤
          ((betheK m t d ν₀ + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
              ∂(ν₀ : Measure (m.Spin → ℝ)) : ℝ) : EReal) := by sorry
