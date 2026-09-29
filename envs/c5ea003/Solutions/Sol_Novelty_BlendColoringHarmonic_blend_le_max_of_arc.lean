-- Prove2me | solution 1 for Novelty.BlendColoringHarmonic.blend_le_max_of_arc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:03:35.299435+00:00
-- url     : https://prove2.me/submissions/7f516f8d-b5b3-41e0-99d1-503904b0a7e9

-- Sol generated from Novelty/BlendColoringHarmonic.lean
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





open Novelty.BlendColoringHarmonic in
theorem solution(w : V → V → ℝ) (c : V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j = 1)
    (hblend : ∀ i, c i = ∑ j, w i j * c j)
    {i₀ : V} (hmax : ∀ x, c x ≤ c i₀) {j : V} (harc : Arc w i₀ j) :
    c j = c i₀ := by
  have hzero : ∑ k, w i₀ k * (c i₀ - c k) = 0 := by
    have hexpand : ∑ k, w i₀ k * (c i₀ - c k)
        = (∑ k, w i₀ k) * c i₀ - ∑ k, w i₀ k * c k := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hexpand, hrow i₀, one_mul, ← hblend i₀, sub_self]
  have hnonneg : ∀ k ∈ (Finset.univ : Finset V), 0 ≤ w i₀ k * (c i₀ - c k) :=
    fun k _ => mul_nonneg (hw i₀ k) (sub_nonneg.mpr (hmax k))
  have hterm : w i₀ j * (c i₀ - c j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero j (Finset.mem_univ j)
  have := mul_eq_zero.mp hterm
  rcases this with h | h
  · exact absurd h (ne_of_gt harc)
  · linarith [sub_eq_zero.mp h]
