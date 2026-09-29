-- Prove2me | Theorems.Thm_BabelCatalog_distributed_catalog_iff
-- name    : BabelCatalog.distributed_catalog_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:16:36.099855+00:00
-- url     : https://prove2.me/theorems/ae8769ca-7ca2-4035-a3d8-643d42be91f8
-- title:
--   Distributed catalog threshold.
-- statement:
--   **Distributed catalog threshold.** A distributed catalog of `N` volumes can
--   injectively encode every sub-collection of the library **iff**
--   `2 ^ (b^L) ≤ (b^L) ^ N`.  (Taking `log_b`, this is the brief's
--   `N ≥ b^L / (L · log_b 2)`.)
--
--   ```lean
--   theorem BabelCatalog.distributed_catalog_iff(b L N : ℕ) :
--       (∃ enc : Finset (Volume b L) → (Fin N → Volume b L), Function.Injective enc)
--         ↔ 2 ^ (b ^ L) ≤ (b ^ L) ^ N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ProofTheoryAndLogic/BabelDiagonalCatalog.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ProofTheoryAndLogic/BabelDiagonalCatalog.lean#L91

-- Thm stub generated from Bridges/ProofTheoryAndLogic/BabelDiagonalCatalog.lean
import Mathlib
import Definitions.Def_Bridges_ProofTheoryAndLogic_BabelDiagonalCatalog

/-!
# The Library of Babel: the Diagonal Catalog and the Distributed-Catalog Threshold

This file formalizes the *cataloguing* questions raised by Borges' **Library of
Babel**, continuing the combinatorial line developed in the catalog's existing
`LibraryOfBabel` files (`Catalog/Novelty/LibraryOfBabel.lean`,
`Catalog/Algebra/LibraryOfBabelProbability.lean`).  Those files count the volumes
(`25 ^ n` of them) and give a bijective *universal catalog* enumerating all
volumes.  Here we ask the deeper question posed in the research brief:

> "Does the Library contain its own complete catalog?"

A *complete catalog* must encode the location of **every sub-collection** of the
library, not merely every individual volume.  We prove:

* `no_single_complete_catalog` — a **Cantor / diagonal** impossibility: no single
  volume can injectively encode all sub-collections (`2 ^ (b^L) > b^L` always).
* `distributed_catalog_iff` — a sharp **cardinality threshold**: a *distributed*
  catalog spread across `N` volumes can injectively encode every sub-collection
  **iff** `2 ^ (b^L) ≤ (b^L) ^ N`.  Taking logs base `b` this is exactly the
  brief's threshold `N ≥ b^L / (L · log_b 2)` (asymptotically `N ≳ b^L/(L log₂ b)`).
* `single_volume_below_threshold` — the `N = 1` instance of the threshold is never
  met, recovering the diagonal impossibility as a special case.

**Menu category (v19a):** *bridge*.  This file bridges **Combinatorics**
(counting volumes) ↔ **Set theory / Logic** (Cantor diagonalization,
`2^κ > κ`) ↔ **Information theory / Computation** (capacity of a distributed
encoding).

`-- !-- Lab Notes -- !--` blocks below document the team loop.
-/

/- -- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).
  Borges' brief claims (a) by a diagonal argument no single volume catalogs the
  whole library, yet (b) a distributed catalog over N volumes can, provided
  N > 25^{1312000} / (1312000 · log₂ 25).  We sharpen "catalog the whole library"
  to "injectively encode every *sub-collection*" (the genuinely hard task — there
  are 2^{b^L} sub-collections), which is the content a real index must address.

EXPERIMENT (Experimenter).
  A single volume holds b^L possible values; the sub-collections number 2^{b^L}.
  Since n < 2^n for all n (`Nat.lt_two_pow_self`), no injection exists — a clean
  Cantor diagonal. For N volumes the capacity is (b^L)^N; an injection between
  fintypes exists iff card ≤ card (`Embedding.nonempty_iff_card_le`), giving the
  exact threshold 2^{b^L} ≤ (b^L)^N.

ANALYSIS (Analyst).
  The threshold is *exact*, not asymptotic: taking log_b of (b^L)^N = b^{LN} and
  comparing with 2^{b^L} = b^{(b^L)·log_b 2} yields N·L ≥ b^L·log_b 2, i.e.
  N ≥ b^L/(L log_b 2) = b^L/(L log₂ b)·log₂ ... matching Borges' figure. The
  brief's "single universal catalog" of *individual* volumes (the existing
  bijection) is consistent; the impossibility appears only for *sub-collections*.

CRITIQUE (Critic).
  Is the statement vacuous for degenerate b,L? No: `Nat.lt_two_pow_self` is
  unconditional, so `no_single_complete_catalog` holds for ALL b,L including
  b=0,1. `distributed_catalog_iff` is a genuine iff with both directions proved
  (forward by `card_le_of_injective`, backward by building an embedding); it is
  not decide-only. The N=1 corollary ties the two results together.

SYNTHESIS (PI).
  A clean trichotomy: 1 volume → impossible (diagonal); N volumes → possible iff a
  sharp power inequality holds. See FUTURE_DIRECTIONS.md for the polynomial-time
  *construction* of a distributed catalog (vs. mere existence proved here).
-- !-- end Lab Notes -- !-- -/

open Function

open BabelCatalog

theorem BabelCatalog.distributed_catalog_iff(b L N : ℕ) :
    (∃ enc : Finset (Volume b L) → (Fin N → Volume b L), Function.Injective enc)
      ↔ 2 ^ (b ^ L) ≤ (b ^ L) ^ N := by sorry
