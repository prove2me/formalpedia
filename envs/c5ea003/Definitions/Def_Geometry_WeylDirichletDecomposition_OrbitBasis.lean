-- Prove2me | Definitions.Def_Geometry_WeylDirichletDecomposition_OrbitBasis
-- name    : Geometry_WeylDirichletDecomposition_OrbitBasis
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T01:01:30.269773+00:00
-- url     : https://prove2.me/theorems/eecabca5-998f-43cd-b142-9de8915e2e04
-- title:
--   Aether Catalog definitions — Geometry_WeylDirichletDecomposition_OrbitBasis
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.WeylDirichletDecomposition.OrbitBasis`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/WeylDirichletDecomposition/OrbitBasis.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_RhoDominantCartan
/-!
# Orbit-basis decomposition for Weyl-invariant functions

The decomposition theorem for twisted Weyl group multiple Dirichlet series separates two
ideas: dominant weights index disjoint Weyl orbits, while shifted Chinta--Gunnells averages
supply invariant functions supported on those orbits.  This file isolates the finite-orbit
algebraic mechanism.  Given a finite family of representatives whose orbits partition a
`G`-set, every invariant function has a unique expansion in the corresponding normalized
orbit indicators.  A Reynolds average supplies the companion projection from arbitrary
functions to invariant functions.

This is an algebraic finite-model counterpart of the paper's analytic decomposition.  The
analytic continuation and convergence hypotheses needed for infinite Kac--Moody Weyl groups
are deliberately not asserted here.

The import of `RhoDominantCartan` links the abstract representative set to the catalog's
simply-laced dominance criterion: in applications, its `IsRhoDominant` predicate provides a
finite combinatorial test for candidate dominant labels.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer): Once dominant labels select exactly one point from every relevant
Weyl orbit, uniqueness of the shifted-average expansion is an orbit-partition theorem, rather
than an analytic accident.  More boldly, Reynolds projection and orbit-basis reconstruction
should be two faces of one finite-group mechanism, valid over every field whose characteristic
does not divide the group order.
EXPERIMENT (Experimenter): Replaced the unavailable infinite Kac--Moody analytic apparatus by
a finite group action.  Normalized orbit indicators were tested on the regular action, where
there is one orbit and invariance is exactly constancy.  The coefficient at an orbit is forced
by evaluation at its representative.
ANALYSIS (Analyst): Three structural ingredients suffice: orbit membership is unchanged by the
group action; unique orbit coverage collapses a finite sum to one term; and reindexing a group
sum proves invariance of Reynolds averaging.  Thus support decomposition (combinatorics) and
averaging (representation theory) meet without analytic assumptions.
CRITIQUE (Critic): This does not formalize the twisted cocycle, convergence, meromorphic
continuation, or the affine extra functional equations.  The boundary is genuine: for an
infinite Weyl group, the Reynolds sum is unavailable and orbit indicators need not satisfy the
paper's analytic hypotheses.  If representatives overlap, uniqueness fails; if the group order
vanishes in the field, normalized averaging fails.  None of the main results is definitional,
and the proofs use orbit transport, unique existence, finite-sum elimination, and extensionality.
SYNTHESIS (Principal Investigator): The verified core is a reusable orbit-basis theorem plus a
finite Reynolds projection.  `RhoDom.dominant_univ_iff` can supply graph-theoretic dominant
labels, while future work must replace finite indicators by convergent shifted
Chinta--Gunnells averages on the complexified Tits cone.
-- !-- end Lab Notes -- !--
-/

namespace WeylDirichlet

open MulAction Finset Classical

section OrbitBasis

variable {G X ι R : Type*} [Group G] [MulAction G X] [Semiring R]

/-- The normalized invariant attached to the orbit of a representative. -/
noncomputable def orbitIndicator (G : Type*) [Group G] [MulAction G X]
    (rep : ι → X) (i : ι) (x : X) : R :=
  if x ∈ MulAction.orbit G (rep i) then 1 else 0






end OrbitBasis

section Reynolds

variable {G X F : Type*} [Group G] [Fintype G] [MulAction G X] [Field F]

/-- Reynolds averaging of a function on a finite `G`-set. -/
noncomputable def reynolds (f : X → F) (x : X) : F :=
  (Fintype.card G : F)⁻¹ * ∑ g : G, f (g • x)




end Reynolds

section Examples

end Examples

end WeylDirichlet


