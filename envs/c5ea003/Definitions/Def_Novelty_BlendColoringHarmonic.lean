-- Prove2me | Definitions.Def_Novelty_BlendColoringHarmonic
-- name    : Novelty_BlendColoringHarmonic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:07:33.82922+00:00
-- url     : https://prove2.me/theorems/4cacaa90-745c-4dd2-9303-e3bfe03c866b
-- title:
--   Aether Catalog definitions — Novelty_BlendColoringHarmonic
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.BlendColoringHarmonic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/BlendColoringHarmonic.lean by skeleton subtraction
import Mathlib

/-!
# Blend colourings of row-stochastic digraphs: the maximum-principle collapse

A **blend colouring** of a finite digraph with nonnegative weights `w` whose rows sum to `1`
is a real colouring `c` that is *harmonic*: the colour of each vertex is the `w`-average of
the colours of its out-neighbours,

`c i = ∑ j, w i j * c j`.

This file proves the collapse theorem that `Novelty/BlendColoringApplications.lean` builds
on: on a strongly connected such digraph a blend colouring must be **constant**.

The proof is the discrete maximum principle.  Pick a vertex `i₀` where `c` is maximal, with
value `M`.  Harmonicity gives `∑ j, w i₀ j * (M - c j) = 0`, a sum of nonnegative terms, so
every term vanishes; hence `c j = M` for every out-neighbour `j` of `i₀` with positive
weight.  Induction along a walk propagates the maximum to every vertex reachable from `i₀`,
and strong connectivity means that is every vertex.

Main results:

* `Arc` : the arc relation `0 < w i j` underlying strong connectivity;
* `blend_le_max_of_arc` : the one-step maximum principle;
* `blend_const` : **a blend colouring of a finite strongly connected row-stochastic digraph
  is constant**.
-/

namespace Novelty.BlendColoringHarmonic

open scoped BigOperators

variable {V : Type*} [Fintype V]

/-- The arc relation of a weight matrix: `i → j` when the weight is strictly positive. -/
def Arc (w : V → V → ℝ) : V → V → Prop := fun i j => 0 < w i j



end Novelty.BlendColoringHarmonic


