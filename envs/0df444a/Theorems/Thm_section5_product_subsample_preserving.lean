-- Prove2me | Theorems.Thm_section5_product_subsample_preserving
-- name    : section5_product_subsample_preserving
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:20:03.410935+00:00
-- url     : https://prove2.me/theorems/524dd716-2518-4f31-b2da-7b95444fffe1
-- title:
--   Product laws under coordinate subsampling
-- statement:
--   Let $I,K$ be finite index sets, $e:K\hookrightarrow I$, and let $
--   u_i,\mu_j$ be probability measures on a measurable space $\Omega$, with $
--   u_{e(j)}=\mu_j$. The coordinate restriction $R(x)=x\circ e$ preserves the indicated product laws:
--
--   $$R_*\Bigl(\bigotimes_{i\in I}
--   u_i\Bigr)=\bigotimes_{j\in K}\mu_j.$$
--
--   This identifies the law of a selected independent subfamily.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5HeraldedMeasurements.lean, lines 21–29.

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem section5_product_subsample_preserving {ι κ Ω : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (μ : κ → Measure Ω) (e : κ ↪ ι) (hμ : ∀ i, ν (e i)=μ i) :
    MeasurePreserving (fun x : ι → Ω => x ∘ e) (Measure.pi ν) (Measure.pi μ) := by sorry
