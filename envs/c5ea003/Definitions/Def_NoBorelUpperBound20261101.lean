-- Prove2me | Definitions.Def_NoBorelUpperBound20261101
-- name    : NoBorelUpperBound20261101
-- status  : Definition
-- author  : @username
-- created : 2026-11-02T02:41:36.929853+00:00
-- url     : https://prove2.me/theorems/57c447a3-87a3-4ca4-93e8-4a2437140158
-- title:
--   Borel upper bounds and real $\ell_1$ coset relations
-- statement:
--   A relation is Borel when its graph is measurable in the Borel sigma algebra of the product topology. Borel reducibility means that a Borel measurable map preserves and reflects the relation on every pair of points. A relation F is an upper bound for the F-sigma equivalence relations when every equivalence relation with an F-sigma graph on every Polish source admits such a reduction to F. This predicate imposes no complexity or equivalence assumption on F by itself.
--
--   The fixed real sequence space is $\ell_1(\mathbb N;\mathbb R)$ with its norm topology. For a real linear subspace H, its additive coset relation is $xE_Hy\iff y-x\in H$. Borel sigma algebras are explicit, and Polish sources range over the ordinary Lean type universe; target universes are arbitrary.
-- source:
--   No Borel upper bound for the F_sigma equivalence relations, research proof note dated 1 November 2026, supplied manuscript UniversalBorelEquivalence-20261101.tex, Section 1, Theorem 1; Section 4, Corollary 4 (using a fixed Banach-space isomorphism to standard real ell_1).

import Definitions.Def_NoUniversalFSigma261031052
import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option autoImplicit false

namespace NoBorelUpperBoundFSigma
universe u v

def IsBorelRelation {X : Type u} [TopologicalSpace X] (E : X → X → Prop) : Prop :=
  @MeasurableSet (X × X) (borel (X × X)) {p | E p.1 p.2}

def BorelReducible {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  ∃ f : X → Y, NoUniversalFSigma.IsBorelMeasurable f ∧ NoUniversalFSigma.IsReduction f E F

def IsFSigmaUpperBound {Y : Type u} [TopologicalSpace Y] (F : Y → Y → Prop) : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [PolishSpace X] (E : Setoid X),
    NoUniversalFSigma.IsFSigmaRelation E.r → BorelReducible E.r F

abbrev RealL1 := lp (fun _ : ℕ => ℝ) 1

def LinearCosetRelation (H : Submodule ℝ RealL1) (x y : RealL1) : Prop :=
  y - x ∈ H

end NoBorelUpperBoundFSigma


