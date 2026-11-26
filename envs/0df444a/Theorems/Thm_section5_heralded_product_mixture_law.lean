-- Prove2me | Theorems.Thm_section5_heralded_product_mixture_law
-- name    : section5_heralded_product_mixture_law
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:21:16.866038+00:00
-- url     : https://prove2.me/theorems/2650a160-2ca2-4b92-bfc8-6a60606669c4
-- title:
--   Heralded mixtures with a common selected marginal
-- statement:
--   Let $T,I,K$ be finite, let $T$ have measurable singletons, and let $w_t$ be extended nonnegative weights summing to $1$. Let $
--   u_{t,i}$ be probability laws on a measurable space $\Omega$, and let $e_t:K\hookrightarrow I$ satisfy $
--   u_{t,e_t(j)}=\mu_j$. Form the tagged mixture $M=\sum_t w_t(\delta_t\otimes\bigotimes_i
--   u_{t,i})$. Then
--
--   $$((t,x)\mapsto x\circ e_t)_*M=\bigotimes_{j\in K}\mu_j.$$
--
--   Thus a common selected marginal survives mixing over the herald.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5HeraldedMeasurements.lean, lines 51–69.

import Mathlib
import Theorems.Thm_section5_product_subsample_preserving
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem section5_heralded_product_mixture_law {T ι κ Ω : Type*}
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] (w : T → ℝ≥0∞) (hw : ∑ t,w t=1)
    (ν : T → ι → Measure Ω) [∀ t i, IsProbabilityMeasure (ν t i)]
    (μ : κ → Measure Ω) (e : T → κ ↪ ι) (hselected : ∀ t j, ν t (e t j)=μ j) :
    Measure.map (fun tx : T × (ι → Ω) => tx.2 ∘ e tx.1)
      (Measure.sum (fun t => w t • Measure.map (fun x : ι → Ω => (t,x)) (Measure.pi (ν t))))=
        Measure.pi μ := by sorry
