-- Prove2me | Definitions.Def_ModNullCompact20261109
-- name    : ModNullCompact20261109
-- status  : Definition
-- author  : @username
-- created : 2026-11-09T09:00:51.903958+00:00
-- url     : https://prove2.me/theorems/e758f150-a9ab-415d-a033-4b0908e0d96b
-- title:
--   Compact groups, normalized Haar probability, and low-complexity cosets
-- statement:
--   A compact metrizable Haar group carries an actual group and topology with continuous multiplication and inversion, a measurable structure equal to the Borel sigma algebra, and one measure satisfying both Mathlib's Haar and probability classes. Commutativity is stated separately, so the common interface also supports the nonabelian amplification result.
--
--   The coset relation is $x^{-1}y\in H$ for an algebraic subgroup $H$. A low-complexity family assigns subgroups to all well-founded tree codes and requires every subgroup to be $\Delta^0_3$, every coset graph to be $\Delta^0_3$, and each graph to be a difference of two $F_\sigma$ sets in the product topology. No measurable dependence on the tree index and no closedness of the subgroup are assumed.
-- source:
--   Universality modulo null sets in the Borel hierarchy, user-supplied unpublished manuscript dated 9 November 2026; SHA-256 48745c75427f83370292c2e4cf91ec06377e80472252db0182599edcd05e2d97, Theorem 1.1, Lemma 3.2, and Section 5.

import Definitions.Def_ModNullCore20261109
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.MetricSpace.Polish

set_option autoImplicit false

namespace ModNullUniversality

structure CompactMetrizableHaarGroup where
  Carrier : Type
  [group : Group Carrier]
  [topology : TopologicalSpace Carrier]
  [compact : CompactSpace Carrier]
  [metrizable : TopologicalSpace.MetrizableSpace Carrier]
  [topologicalGroup : IsTopologicalGroup Carrier]
  [measurable : MeasurableSpace Carrier]
  [borelSpace : BorelSpace Carrier]
  haar : MeasureTheory.Measure Carrier
  [probability : MeasureTheory.IsProbabilityMeasure haar]
  [haarMeasure : MeasureTheory.Measure.IsHaarMeasure haar]

attribute [instance] CompactMetrizableHaarGroup.group CompactMetrizableHaarGroup.topology
  CompactMetrizableHaarGroup.compact CompactMetrizableHaarGroup.metrizable
  CompactMetrizableHaarGroup.topologicalGroup CompactMetrizableHaarGroup.measurable
  CompactMetrizableHaarGroup.borelSpace CompactMetrizableHaarGroup.probability
  CompactMetrizableHaarGroup.haarMeasure

def IsAbelian (K : CompactMetrizableHaarGroup) : Prop :=
  ∀ x y : K.Carrier, x * y = y * x

def CosetRelation (K : CompactMetrizableHaarGroup) (H : Subgroup K.Carrier)
    (x y : K.Carrier) : Prop := x⁻¹ * y ∈ H

def LowComplexityFamily (K : CompactMetrizableHaarGroup)
    (H : WF → Subgroup K.Carrier) : Prop :=
  (∀ T, IsDelta3 (H T : Set K.Carrier)) ∧
  (∀ T, IsDelta3 {p : K.Carrier × K.Carrier | CosetRelation K (H T) p.1 p.2}) ∧
  (∀ T, DifferenceFSigma {p : K.Carrier × K.Carrier | CosetRelation K (H T) p.1 p.2})

end ModNullUniversality


