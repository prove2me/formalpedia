-- Prove2me | Theorems.Thm_SheafCohomologyRobustness_NerveBetti_ker_delta_eq_constants
-- name    : SheafCohomologyRobustness.NerveBetti.ker_delta_eq_constants
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:53:06.528982+00:00
-- url     : https://prove2.me/theorems/e1356f45-c9c6-43a4-93ef-766b22a3777b
-- title:
--   `H⁰` is the line of constants.
-- statement:
--   **`H⁰` is the line of constants.**  On a connected nerve, a `0`-cochain with
--   no jump across any overlap is a constant multiple of the unit certificate.
--
--   ```lean
--   theorem SheafCohomologyRobustness.NerveBetti.ker_delta_eq_constants[Nonempty ι] (hconn : IsConnectedNerve (edgeAdj G)) :
--       LinearMap.ker (delta G) = Submodule.span ℝ {(fun _ => 1 : ι → ℝ)} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/SheafCohomologyRobustness/NerveBetti.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/SheafCohomologyRobustness/NerveBetti.lean#L100

-- Thm stub generated from MachineLearning/SheafCohomologyRobustness/NerveBetti.lean
import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_NerveBetti
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

open SheafCohomologyRobustness
open NerveBetti

open GraphNerve


variable {ι Edge : Type*} (G : NerveGraph ι Edge)

theorem SheafCohomologyRobustness.NerveBetti.ker_delta_eq_constants[Nonempty ι] (hconn : IsConnectedNerve (edgeAdj G)) :
    LinearMap.ker (delta G) = Submodule.span ℝ {(fun _ => 1 : ι → ℝ)} := by sorry
