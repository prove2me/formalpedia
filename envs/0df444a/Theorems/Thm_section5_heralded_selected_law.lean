-- Prove2me | Theorems.Thm_section5_heralded_selected_law
-- name    : section5_heralded_selected_law
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:19:48.923436+00:00
-- url     : https://prove2.me/theorems/08faf242-cf3e-5c54-a588-b3e5c2871f9d
-- title:
--   Independent heralding preserves selected product law
-- statement:
--   Let $T$ be countable with measurable singletons and probability law $
--   u$, let $I,K$ be finite, and let $\mu$ be a probability law on a measurable space $\Omega$. For each $t\in T$, choose an injection $e_t:K\hookrightarrow I$. Under the independent joint law of a herald $t$ and $I$ samples of law $\mu$, selection has law
--
--   $$((t,x)\mapsto x\circ e_t)_*(
--   u\otimes\mu^{\otimes I})=\mu^{\otimes K}.$$
--
--   This justifies independent selection controlled by a herald.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5HeraldedMeasurements.lean, lines 42–49.

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem section5_heralded_selected_law {T ι κ Ω : Type*}
    [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] (ν : Measure T) [IsProbabilityMeasure ν]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (e : T → κ ↪ ι) :
    MeasurePreserving (fun tx : T × (ι → Ω) => tx.2 ∘ e tx.1)
      (ν.prod (Measure.pi (fun _ : ι => μ))) (Measure.pi (fun _ : κ => μ)) := by sorry
