-- Prove2me | Definitions.Def_Novelty_DiscreteCubicalHomotopyBridge
-- name    : Novelty_DiscreteCubicalHomotopyBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:16:18.944714+00:00
-- url     : https://prove2.me/theorems/d717b6bf-f021-468f-80c4-58523ccb72c3
-- title:
--   Aether Catalog definitions — Novelty_DiscreteCubicalHomotopyBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.DiscreteCubicalHomotopyBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/DiscreteCubicalHomotopyBridge.lean by skeleton subtraction
import Mathlib
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
/-
# Bridge: discrete homotopy vs. the classical fundamental group

This companion file connects the synthetic discrete fundamental group developed in
`Catalog.Novelty.DiscreteCubicalHomotopy` with the **classical** fundamental
groupoid.  The overarching goal of discrete homotopy theory (Carranza–Kapulkin)
is to show that the combinatorial invariants of a cubical set agree with the
topological invariants of its geometric realization.

The essential prerequisite for such an isomorphism is *homotopy invariance* of the
classical side: homotopy-equivalent realizations must have the same fundamental
group.  Mirroring the catalog's fundamental-groupoid toolkit (the
`FINAL.Homology` obstruction toolkit, which re-exports that a homotopy equivalence
induces an equivalence of fundamental groupoids), we upgrade that statement here
to an explicit **isomorphism of fundamental groups** at corresponding basepoints,
via the automorphism-group functor.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer):
  H5 (from the main file). The classical fundamental group is a homotopy
  invariant: homotopy-equivalent spaces have isomorphic fundamental groups at
  matching basepoints.  This is the compatibility target that any synthetic
  discrete-homotopy invariant must reproduce for geometric realizations.

Experiment (Experimenter):
  The fundamental group of a space `X` at a basepoint `x` is the automorphism
  group `Aut x` in the fundamental groupoid.  A category equivalence sends objects
  to objects and, being fully faithful, induces group isomorphisms of automorphism
  groups (`Functor.FullyFaithful.autMulEquivOfFullyFaithful`).  Composing with the
  groupoid equivalence induced by a homotopy equivalence yields the desired group
  isomorphism.

Analysis (Analyst):
  The proof is *not* a mere restatement of the groupoid-level lemma: it extracts a
  concrete `MulEquiv` of automorphism groups from an abstract groupoid
  equivalence, which requires the fully-faithful upgrade of the equivalence's
  functor.  This is exactly the step that turns "same homotopy type of groupoid"
  into "isomorphic fundamental groups".

Critique (Critic):
  * Builds a `MulEquiv` via `autMulEquivOfFullyFaithful` and the equivalence's
    fully-faithful functor; no `native_decide`/`rfl`/`True`.
  * Guarded: the conclusion is a genuine existence of a transported basepoint
    together with a group isomorphism, not a vacuous statement.

Synthesis (PI):
  The classical side satisfies homotopy invariance at the level of fundamental
  groups.  Together with the main file (where the synthetic discrete π₁ detects
  exactly the unfilled 2-cubes), this pins down the shape of the sought
  isomorphism between discrete and classical homotopy groups of cubical sets.
-- !-- Lab Notes -- !--
-/

open CategoryTheory
open scoped ContinuousMap

namespace DiscreteCubicalHomotopy.Bridge

/-- The fundamental groupoid of a topological space, as the value of Mathlib's
fundamental-groupoid functor (mirroring the catalog's `FINAL.Homology`
fundamental-groupoid toolkit).  Its automorphism group at a basepoint is the
classical fundamental group `π₁`. -/
noncomputable abbrev fundamentalGroupoidObj (X : Type) [TopologicalSpace X] :=
  FundamentalGroupoid.fundamentalGroupoidFunctor.obj ⟨X⟩



end DiscreteCubicalHomotopy.Bridge


