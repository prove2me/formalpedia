-- Prove2me | solution 1 for Novelty.BlendColoringHarmonic.blend_const
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:06:15.799853+00:00
-- url     : https://prove2.me/submissions/a8f28ff0-c763-4dc5-adb3-d8f501725d12

-- Sol generated from Novelty/BlendColoringHarmonic.lean
import Mathlib
import Definitions.Def_Novelty_BlendColoringHarmonic
import Theorems.Thm_Novelty_BlendColoringHarmonic_blend_le_max_of_arc

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
    (hsc : ∀ i j, Relation.ReflTransGen (Arc w) i j) :
    ∀ i j, c i = c j := by
  intro i j
  obtain ⟨i₀, -, hmax'⟩ :=
    Finset.exists_max_image (Finset.univ : Finset V) c ⟨i, Finset.mem_univ i⟩
  have hmax : ∀ x, c x ≤ c i₀ := fun x => hmax' x (Finset.mem_univ x)
  have hprop : ∀ u v : V, Relation.ReflTransGen (Arc w) u v → c u = c i₀ → c v = c i₀ := by
    intro u v h
    induction h with
    | refl => exact fun hu => hu
    | @tail b v _ hstep ih =>
        intro hu
        have hb : c b = c i₀ := ih hu
        have hmaxb : ∀ x, c x ≤ c b := fun x => by rw [hb]; exact hmax x
        have hv : c v = c b := blend_le_max_of_arc w c hw hrow hblend hmaxb hstep
        rw [hv, hb]
  have hi : c i = c i₀ := hprop i₀ i (hsc i₀ i) rfl
  have hj : c j = c i₀ := hprop i₀ j (hsc i₀ j) rfl
  rw [hi, hj]
