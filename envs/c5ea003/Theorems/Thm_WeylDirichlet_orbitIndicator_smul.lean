-- Prove2me | Theorems.Thm_WeylDirichlet_orbitIndicator_smul
-- name    : WeylDirichlet.orbitIndicator_smul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:05:52.991648+00:00
-- url     : https://prove2.me/theorems/c4b830d1-f750-4d8a-840c-e1306b7a447f
-- title:
--   Orbit indicators are invariant under the group action.
-- statement:
--   Orbit indicators are invariant under the group action.
--
--   ```lean
--   theorem WeylDirichlet.orbitIndicator_smul(rep : ι → X) (i : ι) (g : G) (x : X) :
--       (orbitIndicator G rep i (g • x) : R) = orbitIndicator G rep i x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/WeylDirichletDecomposition/OrbitBasis.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/WeylDirichletDecomposition/OrbitBasis.lean#L61

-- Thm stub generated from Geometry/WeylDirichletDecomposition/OrbitBasis.lean
import Mathlib
import Definitions.Def_Geometry_RhoDominantCartan
import Definitions.Def_Geometry_WeylDirichletDecomposition_OrbitBasis
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

open WeylDirichlet

open MulAction Finset Classical


variable {G X ι R : Type*} [Group G] [MulAction G X] [Semiring R]

theorem WeylDirichlet.orbitIndicator_smul(rep : ι → X) (i : ι) (g : G) (x : X) :
    (orbitIndicator G rep i (g • x) : R) = orbitIndicator G rep i x := by sorry
