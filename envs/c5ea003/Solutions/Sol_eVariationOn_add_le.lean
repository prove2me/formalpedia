-- Prove2me | solution 1 for eVariationOn.add_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:00:43.874891+00:00
-- url     : https://prove2.me/submissions/19e75f86-43ba-4d04-979a-c4c115b600cb

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.Compact
open scoped BigOperators

theorem solution {α E : Type*} [LinearOrder α]
    [SeminormedAddCommGroup E] (f g : α → E) (s : Set α) :
    eVariationOn (f + g) s ≤ eVariationOn f s + eVariationOn g s := by
  refine iSup_le fun p => ?_
  calc (∑ i ∈ Finset.range p.1, edist ((f + g) (p.2.1 (i + 1))) ((f + g) (p.2.1 i)))
      ≤ ∑ i ∈ Finset.range p.1, (edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) +
          edist (g (p.2.1 (i + 1))) (g (p.2.1 i))) := by
        apply Finset.sum_le_sum
        intro i _
        exact edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))) +
          ∑ i ∈ Finset.range p.1, edist (g (p.2.1 (i + 1))) (g (p.2.1 i)) :=
        Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le p.2.2.1 p.2.2.2) (eVariationOn.sum_le p.2.2.1 p.2.2.2)
