-- Prove2me | Theorems.Thm_Novelty_BlendColoringHarmonic_blend_const
-- name    : Novelty.BlendColoringHarmonic.blend_const
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:13:03.78372+00:00
-- url     : https://prove2.me/theorems/f1ef0121-cd23-4787-8bd6-4e444439bcf1
-- title:
--   The blend-colouring collapse.
-- statement:
--   **The blend-colouring collapse.**  On a finite strongly connected digraph with
--   nonnegative row-stochastic weights, every blend (harmonic) colouring is constant.
--
--   ```lean
--   theorem Novelty.BlendColoringHarmonic.blend_const(w : V → V → ℝ) (c : V → ℝ)
--       (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j = 1)
--       (hblend : ∀ i, c i = ∑ j, w i j * c j)
--       (hsc : ∀ i j, Relation.ReflTransGen (Arc w) i j) :
--       ∀ i j, c i = c j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BlendColoringHarmonic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BlendColoringHarmonic.lean#L59

-- Thm stub generated from Novelty/BlendColoringHarmonic.lean
import Mathlib
import Definitions.Def_Novelty_BlendColoringHarmonic

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

open Novelty.BlendColoringHarmonic

open scoped BigOperators

variable {V : Type*} [Fintype V]

theorem Novelty.BlendColoringHarmonic.blend_const(w : V → V → ℝ) (c : V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j = 1)
    (hblend : ∀ i, c i = ∑ j, w i j * c j)
    (hsc : ∀ i j, Relation.ReflTransGen (Arc w) i j) :
    ∀ i j, c i = c j := by sorry
