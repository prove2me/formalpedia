-- Prove2me | solution 1 for SheafCohomologyRobustness.NerveBetti.finrank_nerveH1
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T00:21:45.660118+00:00
-- url     : https://prove2.me/submissions/fae23c79-959f-4608-813e-2c6cc74b9689

-- Sol generated from MachineLearning/SheafCohomologyRobustness/NerveBetti.lean
import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_NerveBetti
import Theorems.Thm_SheafCohomologyRobustness_NerveBetti_ker_delta_eq_constants
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





/-- On a connected nerve, `dim ker δ = 1`. -/
theorem finrank_ker_delta [Nonempty ι] (hconn : IsConnectedNerve (edgeAdj G)) :
    Module.finrank ℝ (LinearMap.ker (delta G)) = 1 := by
  rw [ker_delta_eq_constants G hconn]
  refine finrank_span_singleton ?_
  intro hcon
  have := congrFun hcon (Classical.arbitrary ι)
  simp at this

variable [Fintype ι] [Fintype Edge]

omit [Fintype Edge] in
/-- The space of gluable overlap discrepancies has dimension `|V| − 1`. -/
theorem finrank_range_delta [Nonempty ι] (hconn : IsConnectedNerve (edgeAdj G)) :
    Module.finrank ℝ (LinearMap.range (delta G)) + 1 = Fintype.card ι := by
  have h := LinearMap.finrank_range_add_finrank_ker (delta G)
  rw [finrank_ker_delta G hconn] at h
  simpa using h






open SheafCohomologyRobustness in
theorem solution[Nonempty ι] (hconn : IsConnectedNerve (edgeAdj G)) :
    (Module.finrank ℝ ((Edge → ℝ) ⧸ LinearMap.range (delta G)) : ℤ)
      = (Fintype.card Edge : ℤ) - (Fintype.card ι : ℤ) + 1 := by
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range (delta G))
  have hr := finrank_range_delta G hconn
  have hcard : Module.finrank ℝ (Edge → ℝ) = Fintype.card Edge := by simp
  rw [hcard] at hq
  have hq' : (Module.finrank ℝ ((Edge → ℝ) ⧸ LinearMap.range (delta G)) : ℤ)
      + (Module.finrank ℝ (LinearMap.range (delta G)) : ℤ) = (Fintype.card Edge : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) hq
  have hr' : (Module.finrank ℝ (LinearMap.range (delta G)) : ℤ) + 1
      = (Fintype.card ι : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) hr
  linarith
