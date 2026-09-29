-- Prove2me | Theorems.Thm_ProbabilityTheory_compProd_map_left
-- name    : ProbabilityTheory.compProd_map_left
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T16:47:55.288425+00:00
-- url     : https://prove2.me/theorems/ae7a306f-8975-4b6a-9023-6518bcd8914a
-- title:
--   Composition-product commutes with relabelling the first coordinate
-- statement:
--   Relabelling the first coordinate commutes with forming a composition-product.
--
--   Let $\mu$ be an s-finite measure on $\mathcal A$, let $\iota:\mathcal A\to\mathcal A'$ be measurable, and let $\eta$ be an s-finite kernel from $\mathcal A'$ to $\mathcal B$. Then
--
--   $$
--   (\iota_\#\mu)\otimes\eta \;=\; \big(\iota\times\mathrm{id}\big)_\#\big(\mu\otimes(\eta\circ\iota)\big),
--   $$
--
--   where $\iota_\#$ is the push-forward and $\eta\circ\iota$ is the kernel pulled back along $\iota$.
--
--   Both sides describe the same experiment: draw the first coordinate, relabel it by $\iota$, and then draw the second coordinate from the kernel evaluated at the relabelled point. The only choice is whether the relabelling happens before or after the second coordinate is drawn, and since the kernel is evaluated at the relabelled point either way, the two agree.
--
--   The identity is what one needs to transport a composition-product between two indexings of the same underlying space. A typical use: an interaction history of length $n$ can be indexed by `Fin n` or by an initial segment `Iic (n-1)` of the naturals, and results about the infinite-horizon trajectory measure are naturally stated in the second indexing while the finite-horizon model uses the first.
-- source:
--   Standard property of the composition-product of a measure with a kernel; see Mathlib's ProbabilityTheory.Measure.compProd and Kernel.comap. Used in Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf, Section 4.6 (the canonical bandit model, printed pp. 48-50), to relate the finite-horizon canonical model to the infinite-horizon trajectory model.

import Mathlib.Probability.Kernel.Composition.MeasureCompProd

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem ProbabilityTheory.compProd_map_left {α α' β : Type*}
    {mα : MeasurableSpace α} {mα' : MeasurableSpace α'} {mβ : MeasurableSpace β}
    (μ : Measure α) [SFinite μ]
    {ι : α → α'} (hι : Measurable ι) (η : Kernel α' β) [IsSFiniteKernel η] :
    (μ.map ι) ⊗ₘ η = (μ ⊗ₘ (η.comap ι hι)).map (Prod.map ι id) := by
  sorry
