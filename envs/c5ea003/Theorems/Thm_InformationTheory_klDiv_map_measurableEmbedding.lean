-- Prove2me | Theorems.Thm_InformationTheory_klDiv_map_measurableEmbedding
-- name    : InformationTheory.klDiv_map_measurableEmbedding
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T16:37:20.919752+00:00
-- url     : https://prove2.me/theorems/5830de57-f363-45ae-ba07-b3dee8cb8a0f
-- title:
--   Relative entropy is invariant under a measurable embedding
-- statement:
--   Relative entropy is unchanged by an injective measurable relabelling of the underlying space.
--
--   Let $\mu,\nu$ be finite measures on $(\Omega,\mathcal F)$ and let $f:\Omega\to\mathcal Z$ be a measurable embedding — injective, measurable, with measurable range and measurable inverse on its image. Then
--
--   $$
--   D\big(f_\#\mu \,\|\, f_\#\nu\big) \;=\; D\big(\mu\,\|\,\nu\big),
--   $$
--
--   where $f_\#$ denotes the push-forward.
--
--   This is the equality case of the data-processing inequality. Processing the observation through $f$ discards nothing, because $f$ can be inverted on its range, so no information about the hypothesis $\mu$ versus $\nu$ is lost.
--
--   In practice this is the lemma that lets a divergence be transported along a change of coordinates — for instance identifying a space of histories of length $n+1$ with the product of the histories of length $n$ and the observation of the last round — without tracking densities by hand.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf : Exercise 14.9 (Relative entropy between push-forward measures), printed p. 195, of which this is the case where the map generates the whole sigma-algebra; compare Exercise 14.10 (data processing inequality), printed p. 196, whose equality case this is.

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

open MeasureTheory InformationTheory Set
open scoped ENNReal

theorem InformationTheory.klDiv_map_measurableEmbedding {α β : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {f : α → β} (hf : MeasurableEmbedding f) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  sorry
