-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_20_second_limsup
-- name    : ZeroFreeRRG.Hardcore.lemma_4_20_second_limsup
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T11:00:06.002549+00:00
-- url     : https://prove2.me/theorems/f49ca5e1-41b9-48b5-acb0-acb185bf89c6
-- title:
--   Lemma 4.20: planted free-energy variational upper bound
-- statement:
--   For every reveal rate $s\in[0,1]$, the normalized planted limsup of $\log\mathcal Z_G+\ell_s$ is at most the maximum of the Bethe functional plus the reveal perturbation in equation (29), with the maximum attained.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 31, second inequality in equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
open scoped Classical
open Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore

theorem ZeroFreeRRG.Hardcore.lemma_4_20_second_limsup (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∃ ν₀ ∈ cavityLaws m t,
        (∀ ν ∈ cavityLaws m t,
          betheK m t d ν + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
              ∂(ν : Measure (m.Spin → ℝ)) ≤
          betheK m t d ν₀ + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
              ∂(ν₀ : Measure (m.Spin → ℝ))) ∧
        limsup (fun n : ℕ => (((1 : ℝ) / n *
            plantedPinnedE m t s d n (fun M σ U => Real.log (normZ m t M) + pinnedLL m t M σ U)
              : ℝ) : EReal))
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) ≤
          ((betheK m t d ν₀ + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
              ∂(ν₀ : Measure (m.Spin → ℝ)) : ℝ) : EReal) := by sorry
