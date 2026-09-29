-- Prove2me | solution 1 for FINAL.Topology.homotopyEquiv_trans_of_base
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:49:40.036262+00:00
-- url     : https://prove2.me/submissions/6e308ce3-3140-417f-9b82-737d01c31516

-- Sol generated from Novelty/Topology.lean
import Mathlib
import Definitions.Def_Novelty_Topology
/-
# Topology toolkit for the line-transversal classification

This file collects the purely topological facts used by
`FINAL.LineTransversal`.  Everything here is proved from Mathlib and is stated so
that it can be applied as a black box by the geometric development, in the spirit
of "pre-established topological results".

The central fact is the *section criterion for homotopy equivalence*: a continuous
map `p : T → D` that admits a continuous section `s` (i.e. `p ∘ s = id`) **together
with** a homotopy `s ∘ p ≃ id` is a homotopy equivalence, with `s` and `p` as the
two mutually inverse maps.  Geometrically the homotopy `s ∘ p ≃ id` is supplied by
the convexity of the fibres of the projection from the transversal space onto the
space of directions (each fibre is a convex set, hence the straight-line homotopy
to the chosen section stays inside the fibre).
-/

open scoped ContinuousMap unitInterval

open FINAL.Topology

variable {D T : Type*} [TopologicalSpace D] [TopologicalSpace T]





open FINAL.Topology in
theorem solution{S : Type*} [TopologicalSpace S]
    (e₁ : D ≃ₕ T) (e₂ : D ≃ₕ S) : Nonempty (T ≃ₕ S) :=
  ⟨e₁.symm.trans e₂⟩
