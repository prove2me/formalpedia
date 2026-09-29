-- Prove2me | Theorems.Thm_Novelty_BlendColoringHarmonic_blend_le_max_of_arc
-- name    : Novelty.BlendColoringHarmonic.blend_le_max_of_arc
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:13:11.524229+00:00
-- url     : https://prove2.me/theorems/79bdb182-d6df-4e0c-a20d-3d658d6857e7
-- title:
--   One-step maximum principle.
-- statement:
--   **One-step maximum principle.**  If `c` attains its maximum `c i₀` at `i₀`, then every
--   out-neighbour of `i₀` (an arc of positive weight) also attains it.
--
--   ```lean
--   theorem Novelty.BlendColoringHarmonic.blend_le_max_of_arc(w : V → V → ℝ) (c : V → ℝ)
--       (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j = 1)
--       (hblend : ∀ i, c i = ∑ j, w i j * c j)
--       {i₀ : V} (hmax : ∀ x, c x ≤ c i₀) {j : V} (harc : Arc w i₀ j) :
--       c j = c i₀ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BlendColoringHarmonic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BlendColoringHarmonic.lean#L37

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

theorem Novelty.BlendColoringHarmonic.blend_le_max_of_arc(w : V → V → ℝ) (c : V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j = 1)
    (hblend : ∀ i, c i = ∑ j, w i j * c j)
    {i₀ : V} (hmax : ∀ x, c x ≤ c i₀) {j : V} (harc : Arc w i₀ j) :
    c j = c i₀ := by sorry
