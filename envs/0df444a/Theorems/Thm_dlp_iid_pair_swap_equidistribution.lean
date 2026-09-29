-- Prove2me | Theorems.Thm_dlp_iid_pair_swap_equidistribution
-- name    : dlp_iid_pair_swap_equidistribution
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T03:53:39.160114+00:00
-- url     : https://prove2.me/theorems/842b1829-4564-4d21-9a70-635239af0f01
-- statement:
--   **i.i.d.-pair coordinate-swap equidistribution $(X,Y)\sim(Y,X)$.** For two i.i.d. copies under $\mu\otimes\mu$ and any measurable predicate $P$ on the pair, swapping the two coordinates preserves probabilities: $$\Pr[\,P(X,Y)\,] = \Pr[\,P(Y,X)\,].$$ Proof: $\mathrm{Prod.swap}$ is measure-preserving for $\mu\otimes\mu$ (identical factors), and the swapped event is the swap-preimage of the original. This is the symmetric-copies exchangeability that de la Peña–Montgomery-Smith 1995 eq. (7) invokes: $\{(X_i^{(1)},X_i^{(2)})\}$ has the same joint distribution as the $\sigma$-selected $\{(Z_i^{(1)},Z_i^{(2)})\}$, because per coordinate the two i.i.d. copies are exchangeable under the sign swap.
-- source:
--   de la Peña–Montgomery-Smith, Ann. Probab. 23 (1995) 806–816 (arXiv:math/9309211), eq. (7) equidistribution step, p.5.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.Normed.Module.Basic
open MeasureTheory
open scoped ENNReal

theorem dlp_iid_pair_swap_equidistribution
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (P : α → α → Prop) (hP : MeasurableSet {ab : α × α | P ab.1 ab.2}) :
    (μ.prod μ).real {ab : α × α | P ab.1 ab.2}
      = (μ.prod μ).real {ab : α × α | P ab.2 ab.1} := by sorry
