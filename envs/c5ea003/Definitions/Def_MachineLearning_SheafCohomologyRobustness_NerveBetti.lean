-- Prove2me | Definitions.Def_MachineLearning_SheafCohomologyRobustness_NerveBetti
-- name    : MachineLearning_SheafCohomologyRobustness_NerveBetti
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:58:42.834748+00:00
-- url     : https://prove2.me/theorems/a27cf2fa-e0eb-4333-a77f-e52015219f2c
-- title:
--   Aether Catalog definitions — MachineLearning_SheafCohomologyRobustness_NerveBetti
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.SheafCohomologyRobustness.NerveBetti`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/SheafCohomologyRobustness/NerveBetti.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The Betti Number of a Nerve: `dim H¹ = |E| − |V| + 1`

The previous files computed the first cohomology of three specific nerves: the
path (`H¹ = 0`), the loop (`dim H¹ = 1`), and the doubly periodic torus
(`dim H¹ = 2`, with plaquette relations).  This file proves the general law they
are instances of.

For a **finite oriented nerve graph** `G` — a finite set of cover regions `ι`
(vertices) and a finite set of overlaps `Edge` with endpoints `src`, `tgt` —
the Čech `0`-cochains are `ι → ℝ` and the `1`-cochains are `Edge → ℝ`, with
coboundary `(δ f) e = f (tgt e) − f (src e)`.  The main results:

* `ker_delta_eq_constants` — on a connected nerve the kernel of `δ` is exactly
  the line of constant certificates (`H⁰ ≅ ℝ`);
* `finrank_range_delta` — hence the space of gluable discrepancies has dimension
  `|V| − 1`;
* `finrank_nerveH1_add`, `finrank_nerveH1` — therefore

    `dim H¹(nerve) = |E| − |V| + 1`,

  the **first Betti number** (cycle rank) of the nerve graph: the number of
  independent adversarial obstruction classes equals the number of independent
  loops of the cover.
* `nerveH1_eq_zero_iff_card` — in particular `H¹ = 0` exactly when the nerve has
  `|E| = |V| − 1`, i.e. is a spanning tree: **certified gluing is possible for
  every local datum iff the nerve is acyclic**.

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer, grand challenge): "the number of independent
  adversarial obstructions of a cover is a topological invariant of its nerve,
  equal to the first Betti number `|E| − |V| + 1`."
* Experiment (Experimenter): a spanning-tree decomposition was attempted first
  and proved painful in Lean; the rank–nullity route is far cleaner — the only
  geometric input needed is `H⁰ = ℝ`, i.e. that a connected nerve has no
  nonconstant flat certificate, which is proved by transporting along walks.
* Analysis (Analyst): this explains the earlier computations uniformly.  Loop:
  `|E| = |V|`, Betti `1`, matching `finrank_cyclicH1`.  Path: `|E| = |V| − 1`,
  Betti `0`, matching `H1_path_vanishes`.  Torus: the `2`-dimensional nerve has
  plaquettes, so its `H¹` is the *flat* subspace modulo coboundaries and drops
  from `|V| + 1` to `2`; the discrepancy is exactly the rank of the plaquette
  relations, which is the next conjecture in `FUTURE_DIRECTIONS.md`.
* Critique (Critic): the theorem needs `Nonempty ι` (an empty cover has no
  base region and `H⁰ = 0`), and connectivity is genuinely used — for `k`
  components the correct statement is `|E| − |V| + k`, stated as the corollary
  hypothesis rather than silently assumed.
* Synthesis (PI): adversarial obstruction counting is Betti-number counting.
-/


open Finset

namespace SheafCohomologyRobustness
namespace NerveBetti

open GraphNerve

/-- A finite oriented nerve graph: regions `ι` and overlaps `Edge` with
endpoints. -/
structure NerveGraph (ι : Type*) (Edge : Type*) where
  /-- Source region of an overlap. -/
  src : Edge → ι
  /-- Target region of an overlap. -/
  tgt : Edge → ι

variable {ι Edge : Type*} (G : NerveGraph ι Edge)

/-- Two regions are adjacent when some overlap joins them (in either
orientation). -/
def edgeAdj (i j : ι) : Prop :=
  ∃ e : Edge, (G.src e = i ∧ G.tgt e = j) ∨ (G.src e = j ∧ G.tgt e = i)

/-- The Čech coboundary of the nerve graph. -/
def delta : (ι → ℝ) →ₗ[ℝ] (Edge → ℝ) where
  toFun f := fun e => f (G.tgt e) - f (G.src e)
  map_add' f g := by funext e; simp only [Pi.add_apply]; ring
  map_smul' a f := by
    funext e; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring




variable [Fintype ι] [Fintype Edge]






end NerveBetti
end SheafCohomologyRobustness


