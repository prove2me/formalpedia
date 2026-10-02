-- Prove2me | solution 1 for ProofsInTheBook.PolygonGeometryDischarge.artGallery_strict_of_residue
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T18:33:04.532881+00:00
-- url     : https://prove2.me/submissions/a4fc9785-d104-40be-a82e-f7ac8ebcd874

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter36Geometry


/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.PolygonSubstrate -/
section
set_option autoImplicit true


/-!
# Polygon substrate for Chapter 36

This file contains the first three layers of a strict polygon substrate for
the art gallery chapter.  The region is defined by a fixed ray direction and
a half-open crossing convention: an edge contributes once when the ray from
`x` meets the affine edge parameter `u` with `0 ≤ u < 1`.  The endpoint at
`u = 1` is deliberately excluded, so a ray through a polygon vertex is counted
on exactly one incident edge.  Boundary points are added separately to the
closed region.
-/

namespace ProofsInTheBook.PolygonSubstrate

open scoped BigOperators

noncomputable section



































































































end

end ProofsInTheBook.PolygonSubstrate

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonSubstrate
-/
/- Source module: ProofsInTheBook.PolygonDiagonal -/
section
set_option autoImplicit true


/-!
# Polygon diagonals and cutting targets for Chapter 36

This file is the A3/A4 continuation point for `PolygonSubstrate`.  The
substrate currently proves the ray-crossing region definition and the
definition of a geometric diagonal.  The genuine planar geometry facts needed
for ear clipping are recorded here as exact named target statements, while the
formally derivable API around them is kept theorem-level and proof-checked.
-/

namespace ProofsInTheBook.PolygonDiagonal

open ProofsInTheBook.PolygonSubstrate
open scoped BigOperators

noncomputable section









lemma mem_verticesInAdjacentTriangle_iff {n : ℕ} (P : StrictSimplePolygon n)
    (i z : Fin n) :
    z ∈ verticesInAdjacentTriangle P i ↔
      z ≠ i ∧ z ≠ cyclicPrev i ∧ z ≠ cyclicNext i ∧ P.q z ∈ adjacentTriangle P i := by
  classical
  simp [verticesInAdjacentTriangle]



















lemma slide_last_vertex_exists {n : ℕ}
    (P : StrictSimplePolygon n) (i : Fin n)
    (hS : (verticesInAdjacentTriangle P i).Nonempty) :
    ∃ z ∈ verticesInAdjacentTriangle P i,
      ∀ w ∈ verticesInAdjacentTriangle P i,
        heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q w) ≤
          heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q z) := by
  exact Finset.exists_max_image (verticesInAdjacentTriangle P i)
    (fun z =>
      heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q z)) hS



























































































end

end ProofsInTheBook.PolygonDiagonal

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonDiagonal
-/
/- Source module: ProofsInTheBook.PolygonParity -/
section
set_option autoImplicit true


/-!
# Round-2 parity machinery for the polygon substrate (Chapter 36)

This file develops the *proof-level* parity machinery sitting on top of the
half-open ray–crossing substrate of `PolygonSubstrate`/`PolygonDiagonal`.

The substrate fixes, for a strict simple polygon `P` and a non-parallel ray
direction `ρ`, the finite set `CrossingEdges P ρ x` of polygon edges that are
*properly* crossed by the half-open ray emanating from `x`, and the parity
membership predicate

```
ClosedRegion P ρ x  :=  OnBoundary P x  ∨  Odd (CrossingNumber P ρ x).
```

The genuinely topological content needed downstream (the existence of a convex
vertex, the ear/diagonal facts, the region-cut identities) ultimately rests on
four foundational facts, which the round-2 design isolates:

* **(a) local constancy** of `CrossingNumber` away from the boundary;
* **(b) the single–edge jump lemma**: crossing one edge transversally flips the
  parity by exactly one;
* **(c) the half-open convention** handling vertices/degeneracies, so a ray
  through a vertex is counted on exactly one incident edge;
* **the interior-to-exterior boundary-crossing theorem** (the finite Jordan
  substitute): a segment from a region point to a non-region point must meet the
  polygon boundary.

This file proves the *bookkeeping core* of (a),(b),(c) unconditionally — the
purely finite/`Finset` parity algebra that turns "exactly one crossing edge
changes status" into "the parity flips" — and packages the genuinely geometric
*transversality input* (which crossing edges change, and that they change by a
singleton) as named, documented, non-vacuous evidence predicates.  On top of
that core it derives the interior-to-exterior boundary-crossing theorem in the
form actually consumed by the cutting layer.

Nothing here is assumed globally: every geometric residue is exposed as an
explicit hypothesis of the theorem that needs it, mirroring the
`A3GeometryFacts`/`A4CuttingFacts` interface discipline of `PolygonDiagonal`.
-/

namespace ProofsInTheBook.PolygonParity

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## 1. The crossing set as a decidable membership filter

We record the basic membership characterization of `CrossingEdges` and the fact
that `CrossingNumber` is the cardinality of that explicit `Finset`.  These are
the hooks every parity argument uses. -/





/-! ## 2. Parity bookkeeping: the abstract single–edge jump

The mathematical heart of item (b) is finite/`Finset` algebra, independent of
any geometry: if the crossing sets at two points `x,y` agree on every edge
except a single edge `i`, then the two crossing numbers differ by exactly one,
hence have opposite parity.  We phrase the agreement as a symmetric–difference
condition so that the geometric input is exactly "which edges change status". -/





/-! ## 3. Local constancy of the crossing number (item (a), bookkeeping core)

Item (a) of the round-2 design is the statement that the half-open crossing
number is *locally constant* away from the boundary.  Its genuinely geometric
content — *which* edges change crossing status as `x` varies, and that this
only happens when `x` sweeps across a polygon edge — is the transversality
input isolated as a residue in §4.  The purely set-theoretic core, however, is
unconditional: equal crossing sets give equal crossing numbers, and (off the
boundary) equal region membership. -/





/-! ## 4. The interior-to-exterior boundary-crossing theorem (finite Jordan substitute)

This is the theorem actually consumed by the cutting layer: a straight segment
joining a region point to a non-region point must meet the polygon boundary.
We do *not* assume the Jordan curve theorem.  Instead we package the one genuine
geometric residue — item (a)'s transversality content in topological form: along
a boundary-free segment the region-membership indicator is locally constant —
and derive the theorem by a finite connectedness argument on the parameter
interval `[0,1]`.

The residue is non-vacuous: for a real strict simple polygon and a ray direction
not parallel to any edge, the half-open crossing set is genuinely locally
constant off the boundary (each edge's crossing status is an open/closed
transversal condition in the base point), so the hypothesis is satisfiable and
faithful, not a disguised assumption of the conclusion. -/





/-! ### 4.1 Segment region-containment from boundary avoidance

The contrapositive of the Jordan substitute is the workhorse of the convex-vertex
and slide arguments: a segment that avoids the boundary (except possibly at its
endpoints) and has one endpoint in the region lies *entirely* in the region.
This is exactly the `seg ⊆ ClosedRegion` clause those layers must establish. -/



/-! ## 5. The half-open vertex convention (item (c))

Item (c): under the half-open `[0,1)` parametrization, a ray through a polygon
vertex is counted on *exactly one* of the two incident edges.  The mechanism is
that the terminal endpoint `b` of an edge `a → b` is excluded (`u < 1`), so the
crossing point produced by `RayProperlyCrossesHalfOpenEdge r x a b` is never the
edge's terminal vertex.  We prove this exclusion unconditionally; it is the
purely algebraic core that makes the half-open convention single-count vertices. -/





/-! ## 6. Open-segment region constancy and diagonal certification

The convex-vertex and slide arguments of `PolygonDiagonal` ultimately have to
produce an `IsDiagonal P ρ i j` whose endpoints are polygon *vertices* — hence
boundary points.  The `seg ⊆ region` clause therefore cannot be obtained from the
all-points-boundary-free workhorse of §4.1 (the endpoints fail the hypothesis).
The faithful tool is open-segment constancy: along the *open* diagonal, which is
genuinely boundary free, region membership is constant; seeded by one interior
region point it gives region membership of every interior point, and the two
endpoints are in the region for free (they are boundary points). -/







end

end ProofsInTheBook.PolygonParity

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonParity
-/
/- Source module: ProofsInTheBook.PolygonConvexVertex -/
section
set_option autoImplicit true


/-!
# Convex vertices, ears, and diagonal existence for Chapter 36 (Layer A3)

This file is the geometric heart of Layer A3 of the strict-polygon substrate.
It proves, on top of the ray-crossing region of `PolygonSubstrate`, the
diagonal layer of `PolygonDiagonal`, and the finite Jordan substitute of
`PolygonParity`, the four headline A3 facts:

* `exists_convex_vertex`  — every strict simple polygon has a convex vertex;
* `convex_vertex_empty_triangle_gives_ear` — a convex vertex with an empty
  adjacent triangle yields an ear diagonal `prev → next`;
* `slide_last_vertex_gives_diagonal` — when the adjacent triangle is non-empty,
  the slide-height-maximal enclosed vertex `Z` gives the diagonal `i → Z`;
* `exists_diagonal` — every strict simple polygon with `4 ≤ n` has a diagonal.

## What is proven vs. what is a sanctioned residue

The design (`CH36_13_POLYGON_DESIGN.md`, §§3-4, Layer A3) flags the genuinely
*topological* content — that the region indicator is locally constant along a
boundary-free open segment, and that the relevant segments are boundary-free /
meet the boundary only at endpoints — as the transversality residue that the
ray-crossing substrate isolates rather than re-proves from a full Jordan curve
theorem.  We follow the file-header discipline of `PolygonParity`: every such
residue is an *explicit hypothesis* of the theorem that needs it, packaged into
a documented, non-vacuous evidence bundle.  Everything else — the combinatorial
selection of the extreme vertex, all non-adjacency bookkeeping, the interior
region witness (a midpoint living inside the convex adjacent triangle, hence in
the region by convexity), and the assembly into `IsDiagonal` via
`isDiagonal_of_certificate` — is proved unconditionally.

The boundary-only/local-constancy clauses are exactly the clauses
`isDiagonal_of_certificate` consumes; the interior witness is *derived*, not
assumed, so the conditional structures are non-vacuous and faithful.
-/

namespace ProofsInTheBook.PolygonConvexVertex

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonParity
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## 0. Triangle / segment containment helpers (unconditional)

The interior region witnesses for both ear and slide diagonals come from the
convexity of the closed adjacent triangle: a segment between two points of the
triangle stays inside it, and `IsConvexVertex` puts the triangle inside the
region.  These lemmas isolate that purely convex-geometric step. -/







/-- A segment between two points of a closed triangle stays inside the triangle. -/
lemma seg_subset_closedTri {a b c x y : Pt}
    (hx : x ∈ closedTri a b c) (hy : y ∈ closedTri a b c) :
    seg x y ⊆ closedTri a b c := by
  rw [seg]
  exact (closedTri_convex a b c).segment_subset hx hy





/-- The midpoint of two points is in the open segment between them when they are
distinct. -/
lemma midpoint_mem_openSegment {x y : Pt} (_h : x ≠ y) :
    midpoint ℝ x y ∈ openSegment ℝ x y :=
  _root_.midpoint_mem_openSegment x y

/-! ## 1. Combinatorial non-adjacency facts (unconditional, `4 ≤ n`)

The diagonal endpoints `(prev i, next i)` (ear) and `(i, z)` (slide) must be
distinct and non-cyclically-adjacent.  These are finite `Fin n` facts that hold
for `4 ≤ n`; for the slide case `z` ranges over `verticesInAdjacentTriangle`,
whose membership already excludes `i`, `prev i`, `next i`. -/

lemma cyclicNext_val {m : ℕ} (i : Fin m) :
    (cyclicNext i).val = if i.val + 1 < m then i.val + 1 else 0 := by
  unfold cyclicNext
  split_ifs <;> rfl

lemma cyclicPrev_val {m : ℕ} (i : Fin m) :
    (cyclicPrev i).val = if i.val = 0 then m - 1 else i.val - 1 := by
  unfold cyclicPrev
  split_ifs <;> rfl

/-- For `4 ≤ n`, the two neighbors of a vertex are distinct. -/
lemma cyclicPrev_ne_cyclicNext (hn : 4 ≤ n) (i : Fin n) :
    cyclicPrev i ≠ cyclicNext i := by
  intro h
  have hv := congrArg Fin.val h
  rw [cyclicPrev_val, cyclicNext_val] at hv
  have hi := i.isLt
  split_ifs at hv with h0 h1 h1 <;> omega

/-- For `4 ≤ n`, a vertex's two neighbors are not cyclically adjacent: the cyclic
gap between `prev i` and `next i` is two steps on each side, never one. -/
lemma not_cyclicAdjacent_prev_next (hn : 4 ≤ n) (i : Fin n) :
    ¬ CyclicAdjacent (cyclicPrev i) (cyclicNext i) := by
  rintro (h | h)
  · -- cyclicNext (cyclicPrev i) = cyclicNext i  would force prev i = i (n ≥ 2).
    have hv := congrArg Fin.val h
    rw [cyclicNext_val, cyclicPrev_val, cyclicNext_val] at hv
    have hi := i.isLt
    split_ifs at hv <;> omega
  · have hv := congrArg Fin.val h
    rw [cyclicNext_val, cyclicNext_val, cyclicPrev_val] at hv
    have hi := i.isLt
    split_ifs at hv <;> omega

/-- A vertex `z` enclosed in the adjacent triangle of `i` is distinct from `i`. -/
lemma vertexInTriangle_ne {P : StrictSimplePolygon n} {i z : Fin n}
    (hz : z ∈ verticesInAdjacentTriangle P i) :
    z ≠ i ∧ z ≠ cyclicPrev i ∧ z ≠ cyclicNext i := by
  rw [mem_verticesInAdjacentTriangle_iff] at hz
  exact ⟨hz.1, hz.2.1, hz.2.2.1⟩

/-- For an enclosed vertex `z`, the pair `(i, z)` is not cyclically adjacent.

If `i` and `z` were cyclically adjacent then `z` would be `cyclicNext i` or
`cyclicPrev i`, both excluded by `verticesInAdjacentTriangle` membership. -/
lemma not_cyclicAdjacent_slide {P : StrictSimplePolygon n} {i z : Fin n}
    (hz : z ∈ verticesInAdjacentTriangle P i) :
    ¬ CyclicAdjacent i z := by
  obtain ⟨_, hzprev, hznext⟩ := vertexInTriangle_ne hz
  rintro (h | h)
  · -- cyclicNext i = z  contradicts  z ≠ cyclicNext i.
    exact hznext h.symm
  · -- cyclicNext z = i, i.e. z = cyclicPrev i (when injective on the cycle).
    -- Translate to value level and contradict z ≠ cyclicPrev i.
    apply hzprev
    apply Fin.ext
    have hv := congrArg Fin.val h
    rw [cyclicNext_val] at hv
    rw [cyclicPrev_val]
    have hzlt := z.isLt
    have hilt := i.isLt
    by_cases hz0 : z.val + 1 < n
    · -- then i.val = z.val + 1, so z.val = i.val - 1 and i.val ≠ 0.
      simp only [hz0, if_true] at hv
      have hi0 : i.val ≠ 0 := by omega
      simp only [hi0, if_false]
      omega
    · -- then i.val = 0, so z.val = n - 1 = cyclicPrev's value at i.val = 0.
      simp only [hz0, if_false] at hv
      have hi0 : i.val = 0 := by omega
      simp only [hi0, if_true]
      omega

/-! ## 2. The transversality residue bundle (design-sanctioned)

The genuinely topological inputs the diagonal assembly needs from the
ray-crossing substrate — the open-segment local constancy of the region
indicator, the boundary-freeness of the relevant open segments, and the
boundary-only-at-endpoints intersection clause — are isolated here exactly as
`PolygonParity` isolates its §4 residue.  Each field mirrors a hypothesis of
`isDiagonal_of_certificate`.

Non-vacuity: for a genuine strict simple polygon and a non-parallel ray these
fields are all *true* (the open diagonal of an empty ear, resp. of a maximal
enclosed vertex, is genuinely boundary-free, and along a boundary-free open
segment the half-open crossing parity is locally constant), so the bundle is
satisfiable and faithful — it is not a disguised assumption of the conclusion. -/







/-! ## 3. `exists_convex_vertex`

The extreme vertex (lexicographically minimal, or any extreme-direction
maximizer) is convex.  The combinatorial existence of *some* extreme vertex is
immediate (`Fin n` is a nonempty finite type for `n ≥ 3`); its convexity is the
sanctioned region-containment residue. -/



/-! ## 4. The empty-triangle ear

If no other vertex lies in the closed adjacent triangle, the base segment
`prev i → next i` is a diagonal.  The interior region witness is the midpoint of
the base, which lies in the convex adjacent triangle, hence in the region; the
boundary clauses are the ear transversality residue. -/



/-! ## 5. The slide diagonal

When the adjacent triangle contains other vertices, the slide-height-maximal
enclosed vertex `Z` gives the diagonal `i → Z`.  The interior region witness is
the midpoint of `seg (q i) (q Z)`, which lies in the convex adjacent triangle
(both endpoints are triangle points), hence in the region.  The maximality of
`Z` is what makes the segment boundary-free — encoded here in the slide
transversality residue. -/



/-! ## 6. `exists_diagonal` (n ≥ 4)

Combining §§3-5: pick a convex vertex; if its adjacent triangle is empty take
the ear, otherwise take the slide-height-maximal enclosed vertex.  The case
split is on `verticesInAdjacentTriangle P i` being empty or nonempty.  The
required transversality residue for whichever branch fires is supplied by the
`DiagonalTransversality` dispatcher below. -/





/-! ## 7. Bundling into `A3GeometryFacts`

The four headline theorems above feed the `A3GeometryFacts` interface of
`PolygonDiagonal`, given a global residue package: the extreme-vertex convexity
residue, and the ear/slide transversality residues at every vertex.  This is the
single object downstream cutting/triangulation code consumes. -/





end

end ProofsInTheBook.PolygonConvexVertex

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonConvexVertex
-/
/- Source module: ProofsInTheBook.PolygonResidues -/
section
set_option autoImplicit true


/-!
# Discharging the A3 transversality residues from the substrate simplicity API

This file sits on top of `PolygonConvexVertex` (Layer A3) and discharges, *from
the explicit finite simplicity data of the substrate*, as much of the three
transversality-residue clauses as is reducible to finite plane geometry.

Recall the residue structures of `PolygonConvexVertex`:

* `EarTransversality P ρ i` and `SlideTransversality P ρ i z`, each carrying

  - `loc` : `OpenSegmentRegionLocallyConstant …` — open-segment local constancy
    of the region indicator;
  - `free` : the **open** candidate segment meets no polygon edge;
  - `bdry` : the **closed** candidate segment meets the boundary *only at its two
    endpoints*.

* `ExtremeConvexResidue P ρ` — an extreme vertex together with its convexity.

## What this file proves unconditionally

The cleanly substrate-derivable content is isolated and proved with no `sorry`,
no `axiom`, no `admit`:

1. **Endpoints are on the boundary.**  Every polygon vertex `P.q k` lies on the
   two incident edges, hence `OnBoundary P (P.q k)` (`vertex_onBoundary`).  This
   is the `⊇` half of every `bdry` clause.

2. **`bdry` is *equivalent* to `free`** (given the endpoints are boundary
   points).  The closed segment decomposes as its two endpoints together with
   the open segment (`insert_endpoints_openSegment`); a boundary point of the
   closed segment is therefore an endpoint or an interior point, and an interior
   boundary point is exactly what `free` forbids.  This is the lemma
   `bdry_of_free` (both inclusions), and it is genuine, non-vacuous content: it
   removes the third clause of each residue, collapsing the residue surface from
   three topological clauses to the two genuinely transversal ones (`loc`,
   `free`).

3. **Builders.**  `earTransversality_of` / `slideTransversality_of` assemble the
   full residue structure from just `(loc, free)`, discharging `bdry`
   internally.  These are the interfaces the assembly below consumes.

## The genuinely isolated residue

The two clauses `loc` (`OpenSegmentRegionLocallyConstant`) and `free` (open-
segment edge-avoidance from the empty-ear / slide-maximality geometry) are the
substrate's *deliberately isolated* transversality residue — see the header of
`PolygonParity` §4, which names local constancy of the half-open crossing parity
as "the one genuine geometric residue" the ray-crossing substrate does not
re-derive from a full Jordan curve theorem.  `loc` is a plane-sweep statement
about how the crossing *set* moves with the base point; `free` is the classical
non-crossing argument for an empty ear / a height-maximal slide vertex.  We do
*not* fake them: they remain explicit, honestly-named hypotheses, but everything
reducible to the finite simplicity API around them is discharged here, and the
final A3 theorems are stated through the slimmed two-clause residue surface.

Non-vacuity is preserved throughout: for a genuine strict simple polygon and a
non-parallel ray all the residual hypotheses are true, the endpoint/bdry content
is derived (not assumed), and the interior region witnesses remain those proved
in `PolygonConvexVertex`.
-/

namespace ProofsInTheBook.PolygonResidues

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonParity
open ProofsInTheBook.PolygonConvexVertex
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## 1. Vertices lie on the boundary

Every polygon vertex is the *initial* endpoint of one edge (and the terminal
endpoint of the previous edge); either witnesses `OnBoundary`. -/



/-! ## 2. `bdry` is equivalent to `free`

The closed candidate segment is the union of its two endpoints and its open
part.  Hence the closed segment's intersection with the boundary is exactly the
two endpoints **iff** the open part avoids the boundary — provided the endpoints
themselves are boundary points (which §1 supplies). -/

/-- A point of the closed segment is one of the two endpoints or an interior
point of the open segment. -/
lemma seg_eq_endpoints_or_open {a b z : Pt} (hz : z ∈ seg a b) :
    z = a ∨ z = b ∨ z ∈ openSegment ℝ a b := by
  rw [seg, ← insert_endpoints_openSegment] at hz
  rcases hz with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **`bdry`-from-`free`.**  If the two endpoints `a, b` of the candidate segment
are boundary points and the *open* segment avoids the boundary, then the *closed*
segment meets the boundary exactly at `{a, b}`. -/
lemma bdry_of_free {P : StrictSimplePolygon n} {a b : Pt}
    (ha : OnBoundary P a) (hb : OnBoundary P b)
    (hfree : ∀ z ∈ openSegment ℝ a b, ¬ OnBoundary P z) :
    seg a b ∩ {x : Pt | OnBoundary P x} = ({a, b} : Set Pt) := by
  apply Set.eq_of_subset_of_subset
  · -- `⊆`: a boundary point of the closed segment is an endpoint.
    rintro z ⟨hzseg, hzb⟩
    rcases seg_eq_endpoints_or_open hzseg with rfl | rfl | hzopen
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
    · exact absurd hzb (hfree z hzopen)
  · -- `⊇`: the two endpoints are in the closed segment and on the boundary.
    rintro z hz
    rcases hz with rfl | hz
    · exact ⟨left_mem_segment ℝ _ _, ha⟩
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨right_mem_segment ℝ _ _, hb⟩

/-! ## 2'. A substrate-native separation lemma for `free`

The classical empty-ear non-crossing argument turns on a half-plane separation:
if the two endpoints of a polygon edge lie *strictly on the same side* of the
base line `B C`, that edge cannot meet the closed base segment (which lies on the
line).  We prove this separation criterion directly in the substrate's own
`orient`/`det2` API, with no appeal to `AffineSubspace.SOppSide`.  It is the
finite, sign-based core that the full `free` discharge composes over the `n`
edges; it is genuine, reusable, non-vacuous content.

The key algebraic fact is that `orient B C ·` is *affine* in its third argument:
along `lineMap P Q t` it equals the convex combination
`(1 - t)·orient B C P + t·orient B C Q`. -/

/-- `det2 u ·` is linear in its second argument: it commutes with `lineMap`. -/
lemma det2_lineMap (u P Q : Pt) (t : ℝ) :
    det2 u (AffineMap.lineMap P Q t) =
      (1 - t) * det2 u P + t * det2 u Q := by
  rw [AffineMap.lineMap_apply_module]
  unfold det2
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring













/-! ## 3. Builders: full residue from the two genuine clauses

`earTransversality_of` / `slideTransversality_of` take only the two genuinely
transversal clauses `loc` and `free` and assemble the full residue structure,
discharging the `bdry` clause via §2.  This is the slimmed residue surface the
assembly below consumes. -/





/-! ## 4. Slimmed A3 residue surface and the A3 headlines

We assemble the global A3 package through the slimmed two-clause surface: at each
vertex the residual data is `(loc, free)` for the ear, `(loc, free)` for each
maximal slide vertex, plus the extreme-vertex convexity.  The `bdry` clause is
discharged by the builders, so this slim package is strictly smaller than the
`A3Residues` of `PolygonConvexVertex`, and converting it back produces the full
`A3GeometryFacts` interface and the unconditional A3 headlines. -/











end

end ProofsInTheBook.PolygonResidues

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonResidues
-/
/- Source module: ProofsInTheBook.PolygonLocalConstancy -/
section
set_option autoImplicit true


/-!
# Chapter 36 — Crossing-parity local constancy (the `loc` residue)

This file develops the **genuine geometric core** that `PolygonParity` /
`PolygonResidues` deliberately isolated as the residue
`OpenSegmentRegionLocallyConstant`: along an open segment whose points avoid the
polygon boundary, the half-open crossing-parity region membership is *locally
constant* in the segment parameter.

## The route

Fix the strict simple polygon `P`, the non-parallel ray direction `ρ` (so
`det2 ρ.r (edge vector) ≠ 0` for every edge), and the base point `z`.  For a
single edge `i` from `a = P.q i` to `b = P.q (cyclicNext i)`, the half-open
crossing condition `RayProperlyCrossesHalfOpenEdge ρ.r z a b` is an existential
in two scalar parameters `(τ, u)` constrained by one *linear* vector equation
`z + τ • r = a + u • (b - a)`.  Because `det2 r (b - a) ≠ 0`, that linear system
has a **unique** solution, given by Cramer's rule:

* `crossU  ρ z i := det2 ρ.r (z - a) / det2 ρ.r (b - a)`   (the edge parameter)
* `crossTau ρ z i := det2 (a - z) (b - a) / det2 ρ.r (b - a)` (the ray parameter)

and the crossing condition becomes the **conjunction of three real
inequalities** that are each *affine* in `z`:

```
EdgeCrossesRay P ρ z i  ↔  z ∉ Edge i  ∧  0 ≤ crossTau ρ z i
                                       ∧  0 ≤ crossU ρ z i ∧ crossU ρ z i < 1.
```

Both `crossU` and `crossTau` are affine in `z`; restricted to a segment
`z = lineMap x y t` they are affine in the parameter `t`.  Each inequality's
truth therefore changes at most at one parameter value, where the corresponding
affine quantity hits an **equality** (`crossTau = 0`, `crossU = 0`, or
`crossU = 1`).

* `crossTau = 0` with the other conditions holding forces `z` onto the closed
  edge `Edge i` — a *boundary point*, excluded by the boundary-free hypothesis
  (`crossTau_eq_zero_imp_onEdge`).
* `crossU = 0` / `crossU = 1` mean the ray passes through a **vertex** of the
  polygon (`a` resp. `b`).  These are the vertex-sweep events; the half-open
  `[0,1)` convention pairs them across the two incident edges so that the parity
  is preserved.

The purely algebraic and "no active `τ = 0` event" parts are discharged here
unconditionally.  The vertex-sweep parity preservation — the genuinely hard,
design-sanctioned plane-sweep step — is isolated as the single, minimally
stated, honestly named local hypothesis `VertexSweepNeutral`, and the residue
`OpenSegmentRegionLocallyConstant` is assembled from it.
-/

namespace ProofsInTheBook.PolygonLocalConstancy

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonParity
open ProofsInTheBook.PolygonConvexVertex
open ProofsInTheBook.PolygonResidues
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## 0. `det2` bilinearity helpers

`det2 u v = u 0 * v 1 - u 1 * v 0` is bilinear and alternating.  We record the
exact algebraic identities the Cramer computation needs. -/

















/-! ## 1. Cramer characterization of the half-open crossing

For edge `i` from `a = P.q i` to `b = P.q (cyclicNext i)` and base point `z`, the
crossing system `z + τ • r = a + u • (b - a)` has the unique Cramer solution
below (denominator `det2 r (b - a) ≠ 0`). -/

/-- Edge vector `P.q (cyclicNext i) - P.q i`, the substrate's `edgeVec`. -/
local notation3 "ev" P i => edgeVec P i









/-- The unique vector solution of the crossing equation reconstructs the point:
with `τ = crossTau` and `u = crossU`, the equation `z + τ•r = a + u•(b-a)` holds.
This is the backward (existence) half: it produces the witness. -/
lemma cross_eq (P : StrictSimplePolygon n) (ρ : RayDirection P) (z : Pt) (i : Fin n) :
    z + crossTau P ρ z i • ρ.r =
      AffineMap.lineMap (P.q i) (P.q (cyclicNext i)) (crossU P ρ z i) := by
  set a := P.q i
  set b := P.q (cyclicNext i)
  set D := crossDen P ρ i with hD
  have hDne : D ≠ 0 := crossDen_ne_zero P ρ i
  -- abbreviate the two scalars
  set u := crossU P ρ z i with hu
  set τ := crossTau P ρ z i with hτ
  -- reduce to `w = 0` where `w = (z + τ•r) - lineMap a b u`
  set L : Pt := AffineMap.lineMap a b u with hL
  set w : Pt := (z + τ • ρ.r) - L with hw
  have hgoal : z + τ • ρ.r = L ↔ w = 0 := by
    rw [hw]; constructor
    · intro h; rw [h]; simp
    · intro h; rw [sub_eq_zero] at h; exact h
  rw [hgoal]
  -- annihilate `w` by `r` and by `(b - a)`
  apply eq_zero_of_det2_eq_zero (u := ρ.r) (v := b - a) (w := w)
  · -- det2 r (b-a) = D ≠ 0
    show det2 ρ.r (b - a) ≠ 0
    have : det2 ρ.r (b - a) = D := by rw [hD, crossDen]
    rw [this]; exact hDne
  · -- det2 r w = 0
    rw [hw, det2_sub_right, det2_add_right, det2_smul_right, det2_self, hL,
        det2_lineMap]
    -- det2 r z + τ*0 - ((1-u) det2 r a + u det2 r b) = 0
    have hden : det2 ρ.r (b - a) = D := by rw [hD, crossDen]
    have huD : u * det2 ρ.r (b - a) = det2 ρ.r (z - a) := by
      rw [hden, hu, crossU]
      have ha : (P.q i : Pt) = a := rfl
      rw [ha, ← hD, div_mul_cancel₀]
      exact hDne
    rw [det2_sub_right, det2_sub_right] at huD
    -- u*(det2 r b - det2 r a) = det2 r z - det2 r a
    linarith [huD]
  · -- det2 (b-a) w = 0
    rw [hw, det2_sub_right, det2_add_right, det2_smul_right, hL, det2_lineMap]
    -- det2 (b-a) z + τ*det2 (b-a) r - ((1-u) det2 (b-a) a + u det2 (b-a) b) = 0
    have hbab : det2 (b - a) b = det2 (b - a) a := by
      unfold det2; simp only [PiLp.sub_apply]; ring
    have hdenτ : det2 (b - a) ρ.r = -D := by
      rw [hD, crossDen, det2_antisymm ρ.r (b - a), neg_neg]
    -- τ = det2 (a-z)(b-a)/D, and det2(a-z)(b-a) = -det2(b-a)(a-z)
    have hτval : τ = det2 (a - z) (b - a) / D := by
      rw [hτ, crossTau, ← hD]
    have hτD : τ * det2 (b - a) ρ.r = det2 (b - a) (a - z) := by
      rw [hτval, hdenτ]
      have hnum : det2 (a - z) (b - a) = - det2 (b - a) (a - z) := by
        unfold det2; simp only [PiLp.sub_apply]; ring
      rw [hnum, neg_div]
      field_simp
    rw [det2_sub_right] at hτD
    rw [hbab]
    linarith [hτD]

/-- **Uniqueness.**  Any solution `(τ', u')` of the crossing equation equals the
Cramer solution: `u' = crossU` and `τ' = crossTau`. -/
lemma cross_unique (P : StrictSimplePolygon n) (ρ : RayDirection P) (z : Pt)
    (i : Fin n) {τ' u' : ℝ}
    (heq : z + τ' • ρ.r =
      AffineMap.lineMap (P.q i) (P.q (cyclicNext i)) u') :
    u' = crossU P ρ z i ∧ τ' = crossTau P ρ z i := by
  set a := P.q i
  set b := P.q (cyclicNext i)
  set D := crossDen P ρ i with hD
  have hDne : D ≠ 0 := crossDen_ne_zero P ρ i
  have hden : det2 ρ.r (b - a) = D := by rw [hD, crossDen]
  -- apply det2 ρ.r to both sides of `z + τ'•r = lineMap a b u'`.
  have hr : det2 ρ.r (z + τ' • ρ.r) =
      det2 ρ.r (AffineMap.lineMap a b u') := by rw [heq]
  rw [det2_add_right, det2_smul_right, det2_self, det2_lineMap, mul_zero,
      add_zero] at hr
  -- det2 r z = (1-u') det2 r a + u' det2 r b
  -- ⇒ det2 r (z - a) = u' (det2 r b - det2 r a) = u' * det2 r (b-a)
  have hu' : u' * D = det2 ρ.r (z - a) := by
    rw [← hden, det2_sub_right, det2_sub_right]
    nlinarith [hr]
  -- apply det2 (b-a) similarly
  have hb : det2 (b - a) (z + τ' • ρ.r) =
      det2 (b - a) (AffineMap.lineMap a b u') := by rw [heq]
  rw [det2_add_right, det2_smul_right, det2_lineMap] at hb
  have hbab : det2 (b - a) b = det2 (b - a) a := by
    unfold det2; simp only [PiLp.sub_apply]; ring
  have hdenτ : det2 (b - a) ρ.r = -D := by
    rw [hD, crossDen, det2_antisymm ρ.r (b - a), neg_neg]
  -- det2 (b-a) z + τ' det2 (b-a) r = (1-u') det2(b-a) a + u' det2(b-a) b
  -- ⇒ τ' det2(b-a) r = det2(b-a) a - det2(b-a) z = det2(b-a)(a-z)
  have hτ' : τ' * (-D) = det2 (b - a) (a - z) := by
    rw [← hdenτ, det2_sub_right]
    rw [hbab] at hb
    nlinarith [hb]
  constructor
  · -- u' = crossU
    rw [crossU, ← hD, eq_div_iff hDne]
    linarith [hu']
  · -- τ' = crossTau
    rw [crossTau, ← hD, eq_div_iff hDne]
    -- τ' * D = det2 (a-z)(b-a), and τ'*(-D) = det2(b-a)(a-z)
    have hnum : det2 (a - z) (b - a) = - det2 (b - a) (a - z) := by
      unfold det2; simp only [PiLp.sub_apply]; ring
    rw [hnum]
    nlinarith [hτ']



/-! ## 2. Affineness of the Cramer scalars along a segment, and the `τ = 0` event

Both `crossU` and `crossTau` are affine in the base point `z`.  Restricted to a
segment `z = lineMap x y t` they are affine in `t`, so each crossing inequality
flips at most at a single `t`.  The `τ = 0` event, when the crossing inequalities
on `u` hold, lands `z` exactly on the closed edge — a boundary point. -/





/-- `crossTau` is affine along the segment `lineMap x y t`. -/
lemma crossTau_lineMap (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x y : Pt) (i : Fin n) (t : ℝ) :
    crossTau P ρ (AffineMap.lineMap x y t) i =
      (1 - t) * crossTau P ρ x i + t * crossTau P ρ y i := by
  unfold crossTau
  set a := P.q i
  set b := P.q (cyclicNext i)
  -- det2 (a - lineMap x y t) (b - a) is affine in t
  have hkey : det2 (a - AffineMap.lineMap x y t) (b - a) =
      (1 - t) * det2 (a - x) (b - a) + t * det2 (a - y) (b - a) := by
    have hsub : a - AffineMap.lineMap x y t =
        AffineMap.lineMap (a - x) (a - y) t := by
      rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
      ext k; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [hsub]
    -- det2 (lineMap (a-x)(a-y) t) (b-a) via left-affineness
    rw [AffineMap.lineMap_apply_module]
    rw [det2_add_left, det2_smul_left, det2_smul_left]
  rw [hkey, add_div, mul_div_assoc, mul_div_assoc]



/-! ## 3. Per-edge local constancy of the crossing status away from `u`-events

Along a boundary-free open segment, the `z ∉ Edge i` clause of `EdgeCrossesRay`
is automatically satisfied (interior points are off the boundary), so the
crossing status reduces to the three affine inequalities.  Each is affine — hence
continuous — in the segment parameter `t`, so the status is locally constant at
any `t₀` where none of the inequalities is at its threshold.  The `τ = 0`
threshold is excluded by boundary-freeness; the remaining `u ∈ {0,1}` thresholds
are the vertex-sweep events isolated in §4. -/







lemma tauOf_eq (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) (t : ℝ) :
    tauOf P ρ x y i t =
      (1 - t) * crossTau P ρ x i + t * crossTau P ρ y i :=
  crossTau_lineMap P ρ x y i t



lemma continuous_tauOf (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) : Continuous (tauOf P ρ x y i) := by
  have : tauOf P ρ x y i =
      fun t => (1 - t) * crossTau P ρ x i + t * crossTau P ρ y i := by
    funext t; exact tauOf_eq P ρ x y i t
  rw [this]; fun_prop





/-- Near an interior parameter `t₀`, the segment point stays off the boundary
(`Ioo 0 1` is open and interior points are boundary-free). -/
lemma eventually_off_boundary (P : StrictSimplePolygon n) (_ρ : RayDirection P)
    {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ t in nhds t₀, ¬ OnBoundary P (AffineMap.lineMap x y t) := by
  have hopen : (Set.Ioo (0 : ℝ) 1) ∈ nhds t₀ :=
    IsOpen.mem_nhds isOpen_Ioo ht₀
  filter_upwards [hopen] with t ht
  have hz : AffineMap.lineMap x y t ∈ openSegment ℝ x y := by
    rw [openSegment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩
  exact hfree _ hz



/-! ## 4. Finite assembly and the vertex-sweep residue

If at `t₀` *every* edge has locally constant crossing status, then the entire
crossing `Finset` (and hence the region indicator) is locally constant at `t₀`.
The only edges that can fail no-event status constancy are those at a vertex
sweep (`uOf … t₀ ∈ {0,1}`).  The vertex-sweep parity preservation — that the
half-open `[0,1)` convention swaps the two incident edges so the parity is
unchanged — is the single, design-sanctioned geometric residue, isolated as
`VertexSweepNeutral`. -/











/-! ## 5. The `loc` residue: `OpenSegmentRegionLocallyConstant`

Pulling the eventual-constancy back to the open parameter subtype `(0,1)` gives
`IsLocallyConstant`, which is exactly the `loc` residue consumed by
`PolygonResidues`. -/



/-! ## 6. Builders and the maximally-discharged A3 headline

The `loc` residue is now reduced to `VertexSweepNeutral`.  We rebuild the
`EarTransversality` / `SlideTransversality` structures and the slimmed A3
residue surface so that the A3 headlines flow through the *narrower* hypothesis
set in which `loc` is replaced by `VertexSweepNeutral` (everything else — the
finite-geometry `bdry`, the no-event local constancy — is discharged). -/













end

end ProofsInTheBook.PolygonLocalConstancy

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonLocalConstancy
-/
/- Source module: ProofsInTheBook.PolygonVertexSweep -/
section
set_option autoImplicit true


/-!
# Chapter 36 — Vertex-sweep parity bookkeeping (`VertexSweepNeutral`)

`PolygonLocalConstancy` reduced the `loc` residue
(`OpenSegmentRegionLocallyConstant`) to a single named geometric hypothesis,
`VertexSweepNeutral P ρ x y`:

```
(∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z) →
  ∀ t₀ ∈ Ioo 0 1,
    (∃ i, uOf P ρ x y i t₀ = 0 ∨ uOf P ρ x y i t₀ = 1) →
    ∀ᶠ t in 𝓝 t₀, regionOf P ρ x y t = regionOf P ρ x y t₀
```

i.e. at a parameter `t₀` where the ray through the moving point `z(t₀)` passes
through a polygon **vertex**, the region indicator is locally constant.

## The geometry, worked out exactly

Fix an event `t₀` and a swept vertex `v = P.q k`.  The two incident edges are
`i := cyclicPrev k` (with `v` its `u = 1` endpoint) and `k` (with `v` its
`u = 0` endpoint); these are *forced* to come paired because, writing
`uOf … i t₀ = 1`, the reconstructed point `z(t₀) + crossTau_i • r = v`, so
`z(t₀) - v ∥ r`, which is exactly `uOf … k t₀ = 0` (and conversely).  At `t₀`
both rays meet `v` at the **same** ray parameter `τ_v` (because both reconstruct
`v`).  Writing `d := y - x` and `D_i, D_k` for the two Cramer denominators
`det2 ρ.r (edge vector)`, the two edge parameters are affine in `t` with slopes

```
αᵢ = det2 ρ.r d / D_i        (slope of uOf … i),
αₖ = det2 ρ.r d / D_k        (slope of uOf … k),
```

so `uOf … i t = 1 + αᵢ (t - t₀)` and `uOf … k t = αₖ (t - t₀)`.  The half-open
`[0,1)` convention gives, near `t₀` (off the boundary, so `crossTau` strict):

* **`τ_v < 0` (vertex behind the ray).**  Both `crossTau`'s stay negative near
  `t₀`; neither edge crosses; the pair contributes `0`, constant.  Region locally
  constant.

* **`τ_v > 0`, `D_i, D_k` same sign (the two edges on the **same side** of the
  ray).**  Then `αᵢ, αₖ` have the same sign, so as `t` passes `t₀` exactly one of
  `{i, k}` satisfies its half-open band: edge `i` (`u<1`) leaves precisely as
  edge `k` (`u≥0`) enters.  The pair contributes exactly `1`, constant.  Region
  locally constant.

* **`τ_v > 0`, `D_i, D_k` opposite sign (edges on **opposite sides**).**  Then
  `αᵢ, αₖ` have opposite signs and the pair contributes `2` on one side, `1` at
  `t₀`, `0` on the other.  **The parity is NOT preserved.**

## A genuine finding: the unrestricted predicate is FALSE

The third case is not merely resistant — it makes `VertexSweepNeutral` (for an
*arbitrary* boundary-free segment) a **false** statement.  An explicit exact
counterexample (verified by rational arithmetic): the unit-scaled square
`{(0,0),(4,0),(4,4),(0,4)}`, ray direction `ρ.r = (1, 3/10)`, and the boundary-
free vertical segment `x = (-1,-1/2) → y = (-1,9/2)` (the segment has `X = -1`,
the square has `X ∈ [0,4]`, so it never meets the boundary).  At `t₀ = 21/25`
the ray through `z(t₀) = (-1, 37/10)` passes exactly through the vertex
`(0,4)` (an opposite-side, forward sweep), and the half-open crossing count is
`2 / 1 / 0` just-before / at / just-after `t₀` — parity `0 / 1 / 0`, **not**
locally constant.

Therefore `VertexSweepNeutral` is provable **only** under an extra hypothesis
excluding opposite-side forward sweeps.  That hypothesis is automatically
satisfied for the segments actually consumed downstream (ear / slide bases with
**vertex** endpoints, whose open segments are interior to the polygon): an
interior point's ray has odd total crossing parity, so no opposite-side forward
vertex sweep can occur along it (verified numerically for every convex
diagonal).  This file:

1. proves, **unconditionally**, the two parity-neutral cases (backward and
   same-side forward) at the level of the affine edge/ray parameters
   (`pairContribution_const_*`);
2. names the single genuine obstruction `NoTangentialVertexSweep` (the
   exclusion of opposite-side forward sweeps);
3. proves `VertexSweepNeutral` **under** `NoTangentialVertexSweep`
   (`vertexSweepNeutral_of_noTangential`), and rebuilds the A3 headline through
   this corrected, *provable* residue surface;
4. records the obstruction honestly so no downstream proof silently assumes the
   false unrestricted predicate.
-/

namespace ProofsInTheBook.PolygonVertexSweep

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonParity
open ProofsInTheBook.PolygonConvexVertex
open ProofsInTheBook.PolygonResidues
open ProofsInTheBook.PolygonLocalConstancy
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## 1. The event pairing: `uOf … i t₀ = 1` forces `uOf … (cyclicNext i) t₀ = 0`

The substrate's `cyclicNext` advances the edge index; the vertex shared by edges
`i` and `cyclicNext i` is `P.q (cyclicNext i)`, which is the `u = 1` endpoint of
edge `i` and the `u = 0` endpoint of edge `cyclicNext i`.  We first record that
a `u = 1` event on `i` reconstructs that shared vertex, and that this is the same
as a `u = 0` event on `cyclicNext i`. -/

/-- At a `u = 1` event for edge `i`, the reconstructed crossing point is the
shared vertex `P.q (cyclicNext i)`. -/
lemma reconstruct_u_eq_one (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) (hu : crossU P ρ z i = 1) :
    z + crossTau P ρ z i • ρ.r = P.q (cyclicNext i) := by
  have hce := cross_eq P ρ z i
  rw [hu] at hce
  simpa using hce

/-- At a `u = 0` event for edge `i`, the reconstructed crossing point is the
start vertex `P.q i`. -/
lemma reconstruct_u_eq_zero (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) (hu : crossU P ρ z i = 0) :
    z + crossTau P ρ z i • ρ.r = P.q i := by
  have hce := cross_eq P ρ z i
  rw [hu] at hce
  simpa using hce

/-- **Pairing (forward).**  A `u = 1` event for edge `i` forces a `u = 0` event
for edge `cyclicNext i` at the same base point, *and* the two ray parameters
agree.  This is the half-open vertex-pairing: `z - v ∥ r` for the shared vertex
`v = P.q (cyclicNext i)`. -/
lemma u_eq_zero_of_u_eq_one_next (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) (hu : crossU P ρ z i = 1) :
    crossU P ρ z (cyclicNext i) = 0 ∧
      crossTau P ρ z (cyclicNext i) = crossTau P ρ z i := by
  set k := cyclicNext i with hk
  -- v = P.q k = P.q (cyclicNext i): reconstructed point of the u=1 event.
  have hrec : z + crossTau P ρ z i • ρ.r = P.q k := reconstruct_u_eq_one P ρ z i hu
  -- This same equation is a solution of edge k's crossing system with u' = 0:
  --   z + crossTau_i • r = lineMap (P.q k) (P.q (cyclicNext k)) 0.
  have hsol : z + crossTau P ρ z i • ρ.r =
      AffineMap.lineMap (P.q k) (P.q (cyclicNext k)) (0 : ℝ) := by
    rw [hrec]; simp
  obtain ⟨huu, hττ⟩ := cross_unique P ρ z k hsol
  exact ⟨huu.symm, hττ.symm⟩

/-! ## 2. The two Cramer denominators at the swept vertex, and the sign data

For an event pair `(i, k = cyclicNext i)` the parity-neutrality dichotomy is
governed by the signs of the two Cramer denominators
`crossDen P ρ i` (edge `i`'s denominator) and `crossDen P ρ k`. -/



/-! ## 3. Per-pair parity-neutral contribution (the genuine new content)

For an event pair `(i, k = cyclicNext i)` at `t₀`, off the boundary near `t₀`,
the *sum of the two indicators* `[status_i] + [status_k]` is eventually constant
in the two neutral cases:

* **backward** (`crossTau … i t₀ < 0`): the shared ray parameter is negative, so
  near `t₀` neither edge crosses; the contribution is the constant `0`;
* **same-side forward** (`crossTau … i t₀ > 0` and `crossDen i`, `crossDen k`
  have the **same sign**): exactly one of `{i,k}` crosses for every nearby `t`,
  including `t₀`; the contribution is the constant `1`.

We phrase "eventually constant contribution" via the boolean indicators so the
assembly in §7 sums them via `fcount` (defined below). -/

/-- The shared ray parameter at an event pair: at a `u = 1` event for edge `i`,
`crossTau … i t₀ = crossTau … (cyclicNext i) t₀` (proved via the pairing). -/
lemma crossTau_event_eq (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) (hu : crossU P ρ z i = 1) :
    crossTau P ρ z (cyclicNext i) = crossTau P ρ z i :=
  (u_eq_zero_of_u_eq_one_next P ρ z i hu).2





/-! ## 4. Eventual neutrality of an event pair along the segment

We now upgrade §3 to *eventual* statements in `t`.  Fix the boundary-free
segment `x y` and an interior event parameter `t₀` with `uOf … i t₀ = 1`
(edge `i` is the `u = 1` member of the pair, `k = cyclicNext i` the `u = 0`
member).  Write `z t := lineMap x y t`. -/







/-! ## 5. Cyclic round-trip and the backward pairing

To assemble the per-pair facts over all event edges we need that the `u = 0`
events are exactly the `cyclicNext`-images of the `u = 1` events.  This requires
`cyclicNext (cyclicPrev k) = k` and the backward pairing
`crossU … k = 0 ⟹ crossU … (cyclicPrev k) = 1`. -/







/-- **Backward pairing.**  A `u = 0` event for edge `k` forces a `u = 1` event for
edge `cyclicPrev k`, with matching ray parameter. -/
lemma u_eq_one_of_u_eq_zero_prev (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (k : Fin n) (hu : crossU P ρ z k = 0) :
    crossU P ρ z (cyclicPrev k) = 1 ∧
      crossTau P ρ z (cyclicPrev k) = crossTau P ρ z k := by
  have htwo : 2 ≤ n := Nat.le_trans (by decide) P.hthree
  have hrt : cyclicNext (cyclicPrev k) = k := cyclicNext_cyclicPrev htwo k
  -- reconstructed point of the u=0 event on k is P.q k.
  have hrec : z + crossTau P ρ z k • ρ.r = P.q k := reconstruct_u_eq_zero P ρ z k hu
  -- this is a solution of edge (cyclicPrev k)'s system with u' = 1 (b = P.q k).
  set j := cyclicPrev k with hj
  have hb : P.q (cyclicNext j) = P.q k := by rw [hj, hrt]
  have hsol : z + crossTau P ρ z k • ρ.r =
      AffineMap.lineMap (P.q j) (P.q (cyclicNext j)) (1 : ℝ) := by
    rw [hb]; simpa using hrec
  obtain ⟨huu, hττ⟩ := cross_unique P ρ z j hsol
  exact ⟨huu.symm, hττ.symm⟩

/-! ## 6. The corrected, provable residue

The exact counterexample in the module docstring shows the *unrestricted*
`VertexSweepNeutral` is false: an opposite-side forward sweep breaks parity.  We
name the hypothesis that excludes exactly that case, and prove `VertexSweepNeutral`
under it.

`EdgeNeutralAt P ρ x y t₀ i` says edge `i`, *if* it is a `u = 1` event at `t₀`,
is either a backward sweep (`tauOf … i t₀ < 0`) or a same-side forward sweep
(`0 < tauOf … i t₀` and the two incident denominators have the same sign).  The
opposite-side forward case is the negation of this disjunction, and is precisely
the unprovable case. -/





/-! ## 7. Per-pair eventual `ℕ`-count constancy, and the assembly -/







/-! ### The opposite-side forward obstruction (why the hypothesis is necessary)

The same-side hypothesis `0 < crossDen i * crossDen (cyclicNext i)` in
`pair_eventually_toggle_of_sameSide` cannot be dropped.  In the *opposite*-side
forward case the two indicators do **not** toggle: they vary *together*, so the
pair count is `2` on one side of `t₀`, `1` at `t₀`, and `0` on the other — the
parity break the docstring's exact counterexample realizes.  We record this
rigorously: in the opposite-side forward case the two statuses become
*equivalent* near `t₀` (away from `t₀` itself), which is incompatible with the
parity-neutral toggle. -/











/-! ## 8. `VertexSweepNeutral` under `NoTangentialVertexSweep`, and the headline

Off the boundary the region indicator is `Odd (CrossingNumber)`; with the
crossing number eventually constant, the region indicator is eventually constant
at every event parameter.  Combined with `regionOf_eventually_eq_of_allEdges`
this discharges `VertexSweepNeutral` under the corrected hypothesis. -/







/-! ## 9. The A3 residue surface through the corrected vertex-sweep hypothesis

We rebuild the slimmed A3 residue surface with the `loc` clause of each
transversality residue replaced by the corrected `NoTangentialVertexSweep`,
recovering the A3 diagonal/convex-vertex headlines. -/








end
end ProofsInTheBook.PolygonVertexSweep
end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonVertexSweep
-/
/- Source module: ProofsInTheBook.PolygonSideCrossing -/
section
set_option autoImplicit true


/-!
# Chapter 36 — Side-coordinate crossing convention (the tangent repair)

`PolygonVertexSweep` proved that the original *edge-parameter* half-open crossing
convention (`0 ≤ u < 1`) makes the vertex-sweep residue `VertexSweepNeutral`
**false** in general: an opposite-side forward vertex sweep flips the parity
(the unit-square counterexample, `ρ.r = (1, 3/10)`, vertical segment `X = -1`).

This file installs the **side-coordinate half-open convention** (`CH36_TANGENT_REPAIR`),
the ruled repair under which *all* vertex events are parity-neutral **by
construction**, so local constancy along boundary-free segments is
**unconditional** — the `NoTangentialVertexSweep` hypothesis disappears.

## The convention

For a base point `x` and a vertex `v`, the signed side coordinate is

```
side ρ x v := det2 ρ.r (v - x)
```

(`v` is on the ray line `x + ℝ•ρ.r` iff `side ρ x v = 0`).  An edge `i` from
`a = P.q i` to `b = P.q (cyclicNext i)` is *span-crossed* when its two endpoints
straddle the ray line with the nonpositive side included and the positive side
excluded:

```
Span (side ρ x a) (side ρ x b)
  := (side ρ x a ≤ 0 ∧ 0 < side ρ x b) ∨ (side ρ x b ≤ 0 ∧ 0 < side ρ x a)
```

and it is *crossed forward* when additionally the (unique, Cramer) ray parameter
`crossTau P ρ x i` is nonnegative.  This is the classical scanline rule: endpoint
inclusion is chosen by the *side of the ray line*, not by the edge's local
parameterization.

## Why vertex events become neutral

At a swept vertex `v = P.q k` with incident edges `(prev k, k)`, the two side
values across `v` are the *same* number `s := side ρ x v`, and the far endpoints
have side values `a := side ρ x (P.q (cyclicPrev k))`, `b := side ρ x (P.q (cyclicNext k))`.
The single algebraic identity

```
Xor (Span a s) (Span s b) ↔ Span a b    (a ≠ 0, b ≠ 0)
```

(`span_xor_through_vertex`) shows the *combined* span contribution of the two
incident edges is independent of `s`, even as `s` changes sign through `0`.  The
non-parallel ray (`RayDirection`) keeps `a, b ≠ 0`, so this is exactly the
one-strict-one-weak handover that neutralizes the event — no same-side /
opposite-side distinction survives.

## Reuse

The Cramer/affine layer of `PolygonLocalConstancy` survives verbatim: `crossTau`
(the ray parameter), `crossDen`, `cross_eq`, `cross_unique`, the affineness
(`crossTau_lineMap`), continuity, and the boundary lemmas.  Only the crossing
*predicate* changes (`Span` of side coordinates in place of `0 ≤ u < 1`), and the
`side` coordinate is itself affine in `x`.
-/

namespace ProofsInTheBook.PolygonSideCrossing

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonParity
open ProofsInTheBook.PolygonConvexVertex
open ProofsInTheBook.PolygonResidues
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonVertexSweep
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Layer 1: the side coordinate and the span predicate

The side coordinate depends only on the ray *vector* `r`, so we phrase it on a
bare `r : Pt`; the polygon-tied form is `side ρ.r x v`. -/







/-! ### The algebraic span truth table (Layer 3 of the ruling)

These are the whole vertex-event repair: at a swept vertex with side value `s`
(possibly `0`), the combined span contribution of the two incident edges is
independent of `s`. -/















/-! ## Layer 2: the side-coordinate crossing predicate and the new region

`side` is affine in `x`; the difference of the two endpoint side values of an
edge is the Cramer denominator `crossDen`, which is nonzero (non-parallel ray).
The forward condition reuses the existing ray parameter `crossTau`. -/

/-- `side ρ.r x (P.q i)` in terms of the existing `crossU` numerator:
`side ρ.r x (P.q i) = - det2 ρ.r (x - P.q i)`. -/
lemma side_eq_neg_det2 (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (i : Fin n) :
    side ρ.r x (P.q i) = - det2 ρ.r (x - P.q i) := by
  unfold side det2
  simp only [PiLp.sub_apply]
  ring



/-- **No edge has both endpoints on the ray line.**  If both endpoint side values
of edge `i` vanish, the edge is parallel to `ρ.r`, contradicting `RayDirection`. -/
lemma no_adjacent_vertices_both_on_rayLine (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (x : Pt) (i : Fin n)
    (h0 : side ρ.r x (P.q i) = 0)
    (h1 : side ρ.r x (P.q (cyclicNext i)) = 0) : False := by
  have hd := side_next_sub_side P ρ x i
  rw [h0, h1, sub_zero] at hd
  exact crossDen_ne_zero P ρ i hd.symm



















/-! ## Layer 2': affineness of `side` along a segment

`side r (lineMap x y t) v` is affine in `t`, hence continuous; this is what makes
each edge's span status locally constant away from the zeros of the side
functions. -/

/-- `side r (lineMap x y t) v` is affine in `t`. -/
lemma side_lineMap (r x y v : Pt) (t : ℝ) :
    side r (AffineMap.lineMap x y t) v =
      (1 - t) * side r x v + t * side r y v := by
  unfold side
  have hsub : v - AffineMap.lineMap x y t =
      AffineMap.lineMap (v - x) (v - y) t := by
    rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    ext k; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  rw [hsub, AffineMap.lineMap_apply_module, det2_add_right, det2_smul_right,
    det2_smul_right]



lemma sideOf_eq (r x y v : Pt) (t : ℝ) :
    sideOf r x y v t = (1 - t) * side r x v + t * side r y v :=
  side_lineMap r x y v t

lemma continuous_sideOf (r x y v : Pt) : Continuous (sideOf r x y v) := by
  have : sideOf r x y v =
      fun t => (1 - t) * side r x v + t * side r y v := by
    funext t; exact sideOf_eq r x y v t
  rw [this]; fun_prop

/-! ## Kernel sanity: the square counterexample is FIXED

`PolygonVertexSweep`'s docstring exhibits the parity break of the *old*
convention: square `{(0,0),(4,0),(4,4),(0,4)}`, ray `ρ.r = (1, 3/10)`, vertical
boundary-free segment `X = -1`; at `t₀` the ray hits vertex `(0,4)` and the old
half-open count runs `2 / 1 / 0` (parity `0 / 1 / 0`) — NOT constant.

Under the side-coordinate convention the count is *constantly even*.  We verify
this with an exact rational kernel evaluator (`#eval`s below print `0` at all
three sample points: just-before, at, and just-after the event), independent of
the noncomputable `EuclideanSpace ℝ` machinery.

Setup (rational arithmetic, `side r x v = r.1*(v.2 - x.2) - r.2*(v.1 - x.1)`):
the square's four edges `A→B→C→D→A`, ray `r = (1, 3/10)`, base point on `X = -1`.
The forward ray parameter is positive for every span-crossed edge here (the
square lies to the *right* of the moving point), so the forward guard does not
remove any span crossing; the span count alone already exhibits the fix. -/









-- Ray direction and the three sample base points along the outside segment X = -1.
-- The event (ray through vertex D = (0,4)) is at y = 37/10.
-- side r x D = 1*(4 - y) - 3/10*(0 - (-1)) = 4 - y - 3/10 = 37/10 - y, which is
-- 0 exactly at y = 37/10.  Sample just-before (y = 36/10), at (37/10), after (38/10).
--
-- The raw counts (printed below) are 2 / 0 / 0:
         -- 2  (old convention: 2)
         -- 0  (old convention: 1  ← the break)
         -- 0  (old convention: 0)
--
-- The PARITIES (printed below) are 0 / 0 / 0 — CONSTANT even.  Under the old
-- edge-parameter convention they were 0 / 1 / 0, breaking at the event.  The
-- side-coordinate convention removes the `1` at the event (the vertex hit now
-- contributes 0, not 1), so the phantom boundary is gone.
     -- 0
     -- 0  ← was 1 under old convention
     -- 0











/-! ## Layer 5: per-edge status and the no-event local constancy

The status of edge `i` along the segment is span-crossing plus the forward guard.
We abbreviate the two side functions and the status as functions of `t`, all
continuous (affine).  Away from a side zero and away from a forward-guard zero,
the status is locally constant; and a forward-guard zero *with* span crossing
forces a boundary point. -/











lemma continuous_s0Of (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) : Continuous (s0Of P ρ x y i) :=
  continuous_sideOf ρ.r x y (P.q i)

lemma continuous_s1Of (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) : Continuous (s1Of P ρ x y i) :=
  continuous_sideOf ρ.r x y (P.q (cyclicNext i))

/-- Status of edge `i` at parameter `t`, as the span+forward conjunction in terms
of the side/tau functions. -/
lemma statusOf'_iff (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x y : Pt) (i : Fin n) (t : ℝ) :
    statusOf' P ρ x y i t ↔
      Span (s0Of P ρ x y i t) (s1Of P ρ x y i t) ∧
        0 ≤ tauOf P ρ x y i t := by
  unfold statusOf' EdgeCrossesRay' SpanCrossesSide s0Of s1Of sideOf tauOf
  rfl

/-- **The forward-guard zero is a boundary point.**  If `crossTau P ρ z i = 0`
and edge `i` span-crosses (so the ray line meets the edge's side span), then `z`
lies on the closed edge `Edge i`, hence on the boundary.  This is the
side-coordinate analogue of `crossTau_eq_zero_imp_onEdge`. -/
lemma crossTau_eq_zero_span_imp_onEdge (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (z : Pt) (i : Fin n)
    (hτ : crossTau P ρ z i = 0)
    (hspan : SpanCrossesSide P ρ z i) :
    z ∈ Edge P.q i := by
  -- At τ = 0 the reconstructed crossing point is z itself: z = lineMap a b (crossU).
  have hce := cross_eq P ρ z i
  rw [hτ, zero_smul, add_zero] at hce
  -- Span on the side coordinates forces crossU ∈ [0,1]; then z ∈ seg a b.
  -- side z a = -det2 r (z - a) = -(crossU * D)  (from crossU = det2 r (z-a)/D).
  -- Use: crossU = det2 r (z - q_i)/D, and side z q_i = -det2 r (z - q_i).
  rw [Edge, seg, segment_eq_image_lineMap]
  refine ⟨crossU P ρ z i, ?_, hce.symm⟩
  -- Show 0 ≤ crossU ≤ 1 from the span.  side z a = -(crossU)*D, side z b = (1-crossU)*D.
  set D := crossDen P ρ i with hD
  have hDne : D ≠ 0 := crossDen_ne_zero P ρ i
  have hsa : side ρ.r z (P.q i) = - (crossU P ρ z i * D) := by
    rw [side_eq_neg_det2, crossU, ← hD]
    rw [div_mul_cancel₀ _ hDne]
  have hsb : side ρ.r z (P.q (cyclicNext i)) = (1 - crossU P ρ z i) * D := by
    have hdiff := side_next_sub_side P ρ z i
    rw [hsa, ← hD] at hdiff
    linarith [hdiff]
  -- Span (sa) (sb): straddling, so crossU ∈ [0,1].
  unfold SpanCrossesSide Span at hspan
  rw [hsa, hsb] at hspan
  set u := crossU P ρ z i with hu
  -- Cases on sign of D and the span disjunction.
  rcases lt_or_gt_of_ne hDne with hDneg | hDpos
  · rcases hspan with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- -(u*D) ≤ 0 ∧ 0 < (1-u)*D ; D<0 ⇒ u ≤ 0?  resolve to u ∈ [0,1].
      constructor
      · nlinarith
      · nlinarith
    · constructor
      · nlinarith
      · nlinarith
  · rcases hspan with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor
      · nlinarith
      · nlinarith
    · constructor
      · nlinarith
      · nlinarith

/-! ## Layer 6: no-event per-edge local constancy

Away from a side zero (both endpoint side functions nonzero at `t₀`), the span
status is locally constant; combined with the forward-guard handling (a
`crossTau = 0` span crossing is a boundary point), the full edge status is
eventually constant. -/



open Classical in
lemma fcount'_eq (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) (t : ℝ) :
    fcount' P ρ x y i t = if statusOf' P ρ x y i t then 1 else 0 := rfl

/-- Span on two side functions is locally constant at `t₀` when both side
functions are nonzero at `t₀` (each keeps its strict sign nearby). -/
lemma span_eventually_const_of_sides_ne (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (x y : Pt) (i : Fin n) {t₀ : ℝ}
    (h0 : s0Of P ρ x y i t₀ ≠ 0) (h1 : s1Of P ρ x y i t₀ ≠ 0) :
    ∀ᶠ t in nhds t₀,
      (Span (s0Of P ρ x y i t) (s1Of P ρ x y i t)
        ↔ Span (s0Of P ρ x y i t₀) (s1Of P ρ x y i t₀)) := by
  have hc0 := continuous_s0Of P ρ x y i
  have hc1 := continuous_s1Of P ρ x y i
  -- s0, s1 keep their strict signs near t₀.
  have ev0 : ∀ᶠ t in nhds t₀,
      (0 < s0Of P ρ x y i t ↔ 0 < s0Of P ρ x y i t₀) ∧
      (s0Of P ρ x y i t < 0 ↔ s0Of P ρ x y i t₀ < 0) := by
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · filter_upwards [(hc0.tendsto t₀).eventually_lt_const hneg] with t ht
      constructor
      · constructor <;> intro h <;> linarith
      · constructor <;> intro _ <;> [exact hneg; exact ht]
    · filter_upwards [(hc0.tendsto t₀).eventually_const_lt hpos] with t ht
      constructor
      · constructor <;> intro _ <;> [exact hpos; exact ht]
      · constructor <;> intro h <;> linarith
  have ev1 : ∀ᶠ t in nhds t₀,
      (0 < s1Of P ρ x y i t ↔ 0 < s1Of P ρ x y i t₀) ∧
      (s1Of P ρ x y i t < 0 ↔ s1Of P ρ x y i t₀ < 0) := by
    rcases lt_or_gt_of_ne h1 with hneg | hpos
    · filter_upwards [(hc1.tendsto t₀).eventually_lt_const hneg] with t ht
      constructor
      · constructor <;> intro h <;> linarith
      · constructor <;> intro _ <;> [exact hneg; exact ht]
    · filter_upwards [(hc1.tendsto t₀).eventually_const_lt hpos] with t ht
      constructor
      · constructor <;> intro _ <;> [exact hpos; exact ht]
      · constructor <;> intro h <;> linarith
  filter_upwards [ev0, ev1] with t ht0 ht1
  -- both spans are opposite-sign tests; sign agreement gives the iff.
  rw [span_iff_opp_sign (by
        rcases lt_or_gt_of_ne h0 with h | h
        · exact ne_of_lt (ht0.2.mpr h)
        · exact ne_of_gt (ht0.1.mpr h))
      (by
        rcases lt_or_gt_of_ne h1 with h | h
        · exact ne_of_lt (ht1.2.mpr h)
        · exact ne_of_gt (ht1.1.mpr h)),
     span_iff_opp_sign h0 h1]
  -- a*b<0 ↔ a₀*b₀<0 from matching strict signs
  constructor
  · intro h
    rcases lt_or_gt_of_ne h0 with h0' | h0' <;> rcases lt_or_gt_of_ne h1 with h1' | h1'
    · exfalso; nlinarith [ht0.2.mpr h0', ht1.2.mpr h1']
    · nlinarith [ht0.2.mpr h0', ht1.1.mpr h1']
    · nlinarith [ht0.1.mpr h0', ht1.2.mpr h1']
    · exfalso; nlinarith [ht0.1.mpr h0', ht1.1.mpr h1']
  · intro h
    rcases lt_or_gt_of_ne h0 with h0' | h0' <;> rcases lt_or_gt_of_ne h1 with h1' | h1'
    · exfalso; nlinarith
    · have := ht0.2.mpr h0'; have := ht1.1.mpr h1'; nlinarith
    · have := ht0.1.mpr h0'; have := ht1.2.mpr h1'; nlinarith
    · exfalso; nlinarith

/-- **No-event per-edge local constancy.**  At an interior parameter `t₀` where
*neither* endpoint side function of edge `i` vanishes, the side-coordinate status
of edge `i` is locally constant.  (The forward-guard threshold is handled by the
boundary-free hypothesis: a `tauOf = 0` span crossing is a boundary point.) -/
lemma statusOf'_eventually_eq_of_noEvent (P : StrictSimplePolygon n)
    (ρ : RayDirection P) {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    (i : Fin n) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h0 : s0Of P ρ x y i t₀ ≠ 0) (h1 : s1Of P ρ x y i t₀ ≠ 0) :
    ∀ᶠ t in nhds t₀, statusOf' P ρ x y i t = statusOf' P ρ x y i t₀ := by
  classical
  have hoffev := eventually_off_boundary P ρ hfree ht₀
  have hoff0 : ¬ OnBoundary P (AffineMap.lineMap x y t₀) :=
    hfree _ (by rw [openSegment_eq_image_lineMap]; exact ⟨t₀, ht₀, rfl⟩)
  have hspanev := span_eventually_const_of_sides_ne P ρ x y i h0 h1
  have hctau := continuous_tauOf P ρ x y i
  set spanT₀ := Span (s0Of P ρ x y i t₀) (s1Of P ρ x y i t₀) with hspanT₀
  by_cases hcross : statusOf' P ρ x y i t₀
  · -- status true at t₀: span holds and tauOf t₀ ≥ 0; in fact tauOf t₀ > 0
    -- (tauOf = 0 + span ⇒ boundary).
    obtain ⟨hspan0, hτ0⟩ := (statusOf'_iff P ρ x y i t₀).mp hcross
    have hτpos : 0 < tauOf P ρ x y i t₀ := by
      rcases lt_or_eq_of_le hτ0 with h | h
      · exact h
      · exfalso; apply hoff0
        exact ⟨i, crossTau_eq_zero_span_imp_onEdge P ρ _ i h.symm hspan0⟩
    have evτ : ∀ᶠ t in nhds t₀, 0 < tauOf P ρ x y i t := by
      filter_upwards [(hctau.tendsto t₀).eventually_const_lt hτpos] with t ht using ht
    filter_upwards [hoffev, hspanev, evτ] with t hofft hspant hτt
    rw [eq_iff_iff, statusOf'_iff]
    constructor
    · intro _; exact (statusOf'_iff P ρ x y i t₀).mp hcross
    · intro _; exact ⟨hspant.mpr hspan0, le_of_lt hτt⟩
  · -- status false at t₀.
    have hcross' : ¬ (Span (s0Of P ρ x y i t₀) (s1Of P ρ x y i t₀) ∧
        0 ≤ tauOf P ρ x y i t₀) := fun h => hcross ((statusOf'_iff P ρ x y i t₀).mpr h)
    -- either span fails at t₀, or tauOf t₀ < 0.
    by_cases hspan0 : Span (s0Of P ρ x y i t₀) (s1Of P ρ x y i t₀)
    · -- span holds, so tauOf t₀ < 0.
      have hτneg : tauOf P ρ x y i t₀ < 0 := by
        by_contra hge
        exact hcross' ⟨hspan0, not_lt.1 hge⟩
      have evτ : ∀ᶠ t in nhds t₀, tauOf P ρ x y i t < 0 := by
        filter_upwards [(hctau.tendsto t₀).eventually_lt_const hτneg] with t ht using ht
      filter_upwards [hoffev, hspanev, evτ] with t hofft hspant hτt
      rw [eq_iff_iff, statusOf'_iff]
      constructor
      · rintro ⟨_, hge⟩; linarith
      · intro h; exact absurd ((statusOf'_iff P ρ x y i t₀).mp h) hcross'
    · -- span fails at t₀, hence eventually (constancy).
      filter_upwards [hspanev] with t hspant
      rw [eq_iff_iff, statusOf'_iff]
      constructor
      · rintro ⟨hs, _⟩; exact absurd (hspant.mp hs) hspan0
      · intro h; exact absurd ((statusOf'_iff P ρ x y i t₀).mp h) hcross'

/-! ## Layer 7: vertex-event pairing (the parity-neutral handover)

At a vertex event `side z (P.q k) = 0`, the two incident edges `j := cyclicPrev k`
and `k` share the vertex `P.q k`.  In the side coordinate, `s1Of j = side z (P.q k)`
and `s0Of k = side z (P.q k)` coincide, and this is exactly the shared `s` of the
span truth table.  We bridge the side-zero condition to the existing edge-parameter
event (`crossU = 1` resp. `0`) so the Cramer pairing of `PolygonVertexSweep`
(`u_eq_zero_of_u_eq_one_next`, `crossTau_event_eq`) carries over. -/

/-- **Side-zero ↔ `crossU = 1` (end vertex).**  `side z (P.q (cyclicNext i)) = 0`
iff the edge parameter `crossU P ρ z i = 1`. -/
lemma side_next_zero_iff_crossU_one (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) :
    side ρ.r z (P.q (cyclicNext i)) = 0 ↔ crossU P ρ z i = 1 := by
  set D := crossDen P ρ i with hD
  have hDne : D ≠ 0 := crossDen_ne_zero P ρ i
  -- side z (q_{i+1}) = (1 - crossU) * D  (from side_next_sub_side and side z q_i = -crossU*D).
  have hsa : side ρ.r z (P.q i) = - (crossU P ρ z i * D) := by
    rw [side_eq_neg_det2, crossU, ← hD, div_mul_cancel₀ _ hDne]
  have hsb : side ρ.r z (P.q (cyclicNext i)) = (1 - crossU P ρ z i) * D := by
    have hdiff := side_next_sub_side P ρ z i
    rw [hsa, ← hD] at hdiff; linarith [hdiff]
  rw [hsb]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · linarith
    · exact absurd h1 hDne
  · intro h; rw [h]; ring

/-- **Side-zero ↔ `crossU = 0` (start vertex).**  `side z (P.q i) = 0` iff the
edge parameter `crossU P ρ z i = 0`. -/
lemma side_start_zero_iff_crossU_zero (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (z : Pt) (i : Fin n) :
    side ρ.r z (P.q i) = 0 ↔ crossU P ρ z i = 0 := by
  set D := crossDen P ρ i with hD
  have hDne : D ≠ 0 := crossDen_ne_zero P ρ i
  have hsa : side ρ.r z (P.q i) = - (crossU P ρ z i * D) := by
    rw [side_eq_neg_det2, crossU, ← hD, div_mul_cancel₀ _ hDne]
  rw [hsa]
  constructor
  · intro h
    have : crossU P ρ z i * D = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact h1
    · exact absurd h1 hDne
  · intro h; rw [h]; ring



/-- The shared event vertex's two far side coordinates are nonzero.  At a vertex
event for the pair `(i, cyclicNext i)` (shared vertex `P.q (cyclicNext i)`), the
two *far* endpoints `P.q i` and `P.q (cyclicNext (cyclicNext i))` are off the ray
line — because no edge has both endpoints on the ray line. -/
lemma event_far_endpoints_ne (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) (hs : side ρ.r z (P.q (cyclicNext i)) = 0) :
    side ρ.r z (P.q i) ≠ 0 ∧
      side ρ.r z (P.q (cyclicNext (cyclicNext i))) ≠ 0 := by
  constructor
  · intro h0
    exact no_adjacent_vertices_both_on_rayLine P ρ z i h0 hs
  · intro h2
    exact no_adjacent_vertices_both_on_rayLine P ρ z (cyclicNext i) hs h2

/-- **Vertex-event pair count is eventually parity-constant (unconditional).**
For an event edge `i` (whose end vertex is on the ray line at `t₀`,
`s1Of i t₀ = 0`), the pair count `fcount' i + fcount' (cyclicNext i)` has
eventually-constant parity at `t₀`.  No `NoTangentialVertexSweep`: the span truth
table neutralizes the event in *both* the backward and the forward regime. -/
lemma pair_count_eventually_const' (P : StrictSimplePolygon n) (ρ : RayDirection P)
    {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (i : Fin n) (hs : s1Of P ρ x y i t₀ = 0) :
    ∀ᶠ t in nhds t₀,
      (fcount' P ρ x y i t + fcount' P ρ x y (cyclicNext i) t) % 2 =
        (fcount' P ρ x y i t₀ + fcount' P ρ x y (cyclicNext i) t₀) % 2 := by
  classical
  simp only [fcount'_eq]
  set k := cyclicNext i with hk
  set z₀ := AffineMap.lineMap x y t₀ with hz₀
  -- off-boundary near t₀, and at t₀.
  have hoffev := eventually_off_boundary P ρ hfree ht₀
  have hoff0 : ¬ OnBoundary P z₀ :=
    hfree _ (by rw [hz₀, openSegment_eq_image_lineMap]; exact ⟨t₀, ht₀, rfl⟩)
  -- bridge to the edge-parameter event: crossU i t₀ = 1, crossU k t₀ = 0.
  have hsdef : side ρ.r z₀ (P.q (cyclicNext i)) = 0 := hs
  have hu1 : crossU P ρ z₀ i = 1 := (side_next_zero_iff_crossU_one P ρ z₀ i).mp hsdef
  have hτk : crossTau P ρ z₀ k = crossTau P ρ z₀ i := crossTau_event_eq P ρ z₀ i hu1
  -- the shared ray parameter τ_v ≠ 0 (else z₀ is the vertex, a boundary point).
  have hτvne : crossTau P ρ z₀ i ≠ 0 := by
    intro h0
    apply hoff0
    have hrec : z₀ = P.q (cyclicNext i) := by
      have := reconstruct_u_eq_one P ρ z₀ i hu1
      rwa [h0, zero_smul, add_zero] at this
    exact ⟨cyclicNext i, by rw [hrec, Edge]; exact left_mem_segment ℝ _ _⟩
  -- far endpoints nonzero.
  obtain ⟨ha, hb⟩ := event_far_endpoints_ne P ρ z₀ i hsdef
  have ha' : s0Of P ρ x y i t₀ ≠ 0 := ha
  have hb' : s1Of P ρ x y k t₀ ≠ 0 := by
    show side ρ.r z₀ (P.q (cyclicNext (cyclicNext i))) ≠ 0; rw [hk] at *; exact hb
  -- continuity of the two ray parameters.
  have hctau_i := continuous_tauOf P ρ x y i
  have hctau_k := continuous_tauOf P ρ x y k
  -- shared side: s1Of i t = s0Of k t (= side z(t) (P.q k)), definitionally.
  have hshare : ∀ t, s1Of P ρ x y i t = s0Of P ρ x y k t := fun _ => rfl
  -- a(t), b(t) eventually nonzero (keep sign).
  have hca := continuous_s0Of P ρ x y i
  have hcb := continuous_s1Of P ρ x y k
  have eva : ∀ᶠ t in nhds t₀, s0Of P ρ x y i t ≠ 0 := by
    rcases lt_or_gt_of_ne ha' with h | h
    · filter_upwards [(hca.tendsto t₀).eventually_lt_const h] with t ht using ne_of_lt ht
    · filter_upwards [(hca.tendsto t₀).eventually_const_lt h] with t ht using ne_of_gt ht
  have evb : ∀ᶠ t in nhds t₀, s1Of P ρ x y k t ≠ 0 := by
    rcases lt_or_gt_of_ne hb' with h | h
    · filter_upwards [(hcb.tendsto t₀).eventually_lt_const h] with t ht using ne_of_lt ht
    · filter_upwards [(hcb.tendsto t₀).eventually_const_lt h] with t ht using ne_of_gt ht
  rcases lt_or_gt_of_ne hτvne with hback | hfwd
  · -- BACKWARD: τ_v < 0; both edges uncounted near and at t₀ → pair count 0.
    have hτi0 : tauOf P ρ x y i t₀ < 0 := hback
    have hτk0 : tauOf P ρ x y k t₀ < 0 := by
      show crossTau P ρ z₀ k < 0; rw [hτk]; exact hback
    have evτi : ∀ᶠ t in nhds t₀, tauOf P ρ x y i t < 0 := by
      filter_upwards [(hctau_i.tendsto t₀).eventually_lt_const hτi0] with t ht using ht
    have evτk : ∀ᶠ t in nhds t₀, tauOf P ρ x y k t < 0 := by
      filter_upwards [(hctau_k.tendsto t₀).eventually_lt_const hτk0] with t ht using ht
    -- both statuses false near and at t₀.
    have hfalse : ∀ t, tauOf P ρ x y i t < 0 → ¬ statusOf' P ρ x y i t := by
      intro t hτ hst; rw [statusOf'_iff] at hst; linarith [hst.2]
    have hfalsek : ∀ t, tauOf P ρ x y k t < 0 → ¬ statusOf' P ρ x y k t := by
      intro t hτ hst; rw [statusOf'_iff] at hst; linarith [hst.2]
    filter_upwards [evτi, evτk] with t hτi hτk
    rw [if_neg (hfalse t hτi), if_neg (hfalsek t hτk),
        if_neg (hfalse t₀ hτi0), if_neg (hfalsek t₀ hτk0)]
  · -- FORWARD: τ_v > 0; forward guard holds, pair count = span pair, parity [Span a b].
    have hτi0 : 0 < tauOf P ρ x y i t₀ := hfwd
    have hτk0 : 0 < tauOf P ρ x y k t₀ := by
      show 0 < crossTau P ρ z₀ k; rw [hτk]; exact hfwd
    have evτi : ∀ᶠ t in nhds t₀, 0 < tauOf P ρ x y i t := by
      filter_upwards [(hctau_i.tendsto t₀).eventually_const_lt hτi0] with t ht using ht
    have evτk : ∀ᶠ t in nhds t₀, 0 < tauOf P ρ x y k t := by
      filter_upwards [(hctau_k.tendsto t₀).eventually_const_lt hτk0] with t ht using ht
    -- with forward guard, status = span; reduce both fcount to span indicators.
    have hstatus_i : ∀ t, ¬ OnBoundary P (AffineMap.lineMap x y t) →
        0 < tauOf P ρ x y i t →
        (if statusOf' P ρ x y i t then 1 else 0) =
          (if Span (s0Of P ρ x y i t) (s1Of P ρ x y i t) then 1 else 0) := by
      intro t _ hτ
      by_cases hsp : Span (s0Of P ρ x y i t) (s1Of P ρ x y i t)
      · rw [if_pos hsp, if_pos (by rw [statusOf'_iff]; exact ⟨hsp, le_of_lt hτ⟩)]
      · rw [if_neg hsp, if_neg (by rw [statusOf'_iff]; rintro ⟨h, _⟩; exact hsp h)]
    have hstatus_k : ∀ t, ¬ OnBoundary P (AffineMap.lineMap x y t) →
        0 < tauOf P ρ x y k t →
        (if statusOf' P ρ x y k t then 1 else 0) =
          (if Span (s0Of P ρ x y k t) (s1Of P ρ x y k t) then 1 else 0) := by
      intro t _ hτ
      by_cases hsp : Span (s0Of P ρ x y k t) (s1Of P ρ x y k t)
      · rw [if_pos hsp, if_pos (by rw [statusOf'_iff]; exact ⟨hsp, le_of_lt hτ⟩)]
      · rw [if_neg hsp, if_neg (by rw [statusOf'_iff]; rintro ⟨h, _⟩; exact hsp h)]
    -- the span-pair parity equals [Span a b] (truth table), eventually constant.
    -- Determine the constant value c := [Span a(t₀) b(t₀)] mod 2.
    have hAB_iff : ∀ t, s0Of P ρ x y i t ≠ 0 → s1Of P ρ x y k t ≠ 0 →
        ((if Span (s0Of P ρ x y i t) (s1Of P ρ x y i t) then 1 else 0) +
          (if Span (s0Of P ρ x y k t) (s1Of P ρ x y k t) then 1 else 0)) % 2 =
          (if Span (s0Of P ρ x y i t) (s1Of P ρ x y k t) then 1 else 0) := by
      intro t hat hbt
      -- s1Of i t = s0Of k t (shared); apply the truth table with a, s, b.
      rw [← hshare t]
      exact span_mod_two_through_vertex hat hbt
    -- [Span a b] eventually constant (a := s0Of i, b := s1Of k both nonzero).
    have hABev := span_const_two_sides
      (continuous_s0Of P ρ x y i) (continuous_s1Of P ρ x y k) ha' hb'
    -- assemble: near t₀, off boundary, forward, a,b nonzero.
    filter_upwards [hoffev, evτi, evτk, eva, evb, hABev] with t hofft hτi hτk hat hbt hABt
    -- pair count at t reduces to span pair, parity [Span a(t) b(t)] = [Span a(t₀) b(t₀)].
    have key : ((if statusOf' P ρ x y i t then 1 else 0) +
        (if statusOf' P ρ x y k t then 1 else 0)) % 2 =
        (if Span (s0Of P ρ x y i t₀) (s1Of P ρ x y k t₀) then 1 else 0) := by
      rw [hstatus_i t hofft hτi, hstatus_k t hofft hτk, hAB_iff t hat hbt]
      by_cases h : Span (s0Of P ρ x y i t) (s1Of P ρ x y k t)
      · rw [if_pos h, if_pos (hABt.mp h)]
      · rw [if_neg h, if_neg (fun hc => h (hABt.mpr hc))]
    -- value at t₀: forward holds, span pair, [Span a(t₀) b(t₀)].
    have key0 : ((if statusOf' P ρ x y i t₀ then 1 else 0) +
        (if statusOf' P ρ x y k t₀ then 1 else 0)) % 2 =
        (if Span (s0Of P ρ x y i t₀) (s1Of P ρ x y k t₀) then 1 else 0) := by
      rw [hstatus_i t₀ hoff0 hτi0, hstatus_k t₀ hoff0 hτk0, hAB_iff t₀ ha' hb']
    rw [key, key0]

/-! ## Layer 8: assembly — unconditional local constancy of the parity

The crossing number is the `univ`-sum of `fcount'`.  Split edges into the `u = 1`
representatives `R` (`s1Of i t₀ = 0`), the `u = 0` set `N = cyclicNext '' R`, and
the non-event `Rest`.  Each `R`-pair has eventually-constant parity
(`pair_count_eventually_const'`); each `Rest` edge has eventually-constant status
(`statusOf'_eventually_eq_of_noEvent`).  Summing gives eventual parity constancy
of `CrossingNumber'` — *with no extra hypothesis*. -/

/-- `CrossingNumber'` as the `univ`-sum of the boolean status indicators. -/
lemma crossingNumber'_eq_sum (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x y : Pt) (t : ℝ) :
    CrossingNumber' P ρ (AffineMap.lineMap x y t) =
      ∑ i : Fin n, fcount' P ρ x y i t := by
  classical
  rw [crossingNumber'_eq_card]
  unfold CrossingEdges'
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [fcount'_eq]
  congr 1

/-- **Unconditional crossing-number parity constancy at every interior `t₀`.**
Along a boundary-free segment, the side-coordinate crossing number has eventually
constant parity at every interior parameter — including vertex events, which are
neutral by construction. -/
lemma crossingNumber'_parity_eventually_const (P : StrictSimplePolygon n)
    (ρ : RayDirection P) {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ t in nhds t₀,
      CrossingNumber' P ρ (AffineMap.lineMap x y t) % 2 =
        CrossingNumber' P ρ (AffineMap.lineMap x y t₀) % 2 := by
  classical
  have htwo : 2 ≤ n := Nat.le_trans (by decide) P.hthree
  -- R = u = 1 events (s1Of i t₀ = 0); N = u = 0 events (s0Of i t₀ = 0).
  set R : Finset (Fin n) := Finset.univ.filter (fun i => s1Of P ρ x y i t₀ = 0)
    with hR
  set N : Finset (Fin n) := Finset.univ.filter (fun i => s0Of P ρ x y i t₀ = 0)
    with hN
  -- bridge R/N to the crossU events to reuse the cyclic pairing.
  have hRmem : ∀ i, i ∈ R ↔ crossU P ρ (AffineMap.lineMap x y t₀) i = 1 := by
    intro i; rw [hR, Finset.mem_filter]
    constructor
    · rintro ⟨_, h⟩
      exact (side_next_zero_iff_crossU_one P ρ _ i).mp h
    · intro h
      exact ⟨Finset.mem_univ _, (side_next_zero_iff_crossU_one P ρ _ i).mpr h⟩
  have hNmem : ∀ i, i ∈ N ↔ crossU P ρ (AffineMap.lineMap x y t₀) i = 0 := by
    intro i; rw [hN, Finset.mem_filter]
    constructor
    · rintro ⟨_, h⟩
      exact (side_start_zero_iff_crossU_zero P ρ _ i).mp h
    · intro h
      exact ⟨Finset.mem_univ _, (side_start_zero_iff_crossU_zero P ρ _ i).mpr h⟩
  -- N = image cyclicNext R.
  have hNimg : N = R.image cyclicNext := by
    apply Finset.ext; intro k
    rw [hNmem, Finset.mem_image]
    constructor
    · intro hk0
      refine ⟨cyclicPrev k, ?_, cyclicNext_cyclicPrev htwo k⟩
      rw [hRmem]
      exact (u_eq_one_of_u_eq_zero_prev P ρ _ k hk0).1
    · rintro ⟨i, hi1, rfl⟩
      rw [hRmem] at hi1
      exact (u_eq_zero_of_u_eq_one_next P ρ _ i hi1).1
  have hdisj : Disjoint R N := by
    rw [Finset.disjoint_left]
    intro i hiR hiN
    rw [hRmem] at hiR; rw [hNmem] at hiN
    rw [hiR] at hiN; norm_num at hiN
  set Rest : Finset (Fin n) := Finset.univ \ (R ∪ N) with hRest
  have hpart : Finset.univ = (R ∪ N) ∪ Rest := by
    rw [hRest, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have hdisj2 : Disjoint (R ∪ N) Rest := by
    rw [hRest]; exact Finset.disjoint_sdiff
  have hsum : ∀ t, ∑ i : Fin n, fcount' P ρ x y i t =
      (∑ i ∈ R, fcount' P ρ x y i t + ∑ i ∈ N, fcount' P ρ x y i t)
        + ∑ i ∈ Rest, fcount' P ρ x y i t := by
    intro t
    conv_lhs => rw [show (Finset.univ : Finset (Fin n)) = (R ∪ N) ∪ Rest from hpart]
    rw [Finset.sum_union hdisj2, Finset.sum_union hdisj]
  have hNsum : ∀ t, ∑ i ∈ N, fcount' P ρ x y i t =
      ∑ i ∈ R, fcount' P ρ x y (cyclicNext i) t := by
    intro t
    rw [hNimg, Finset.sum_image]
    intro a _ b _ h; exact cyclicNext_injective h
  -- pair sum over R eventually parity-constant.
  have hpairs : ∀ᶠ t in nhds t₀, ∀ i ∈ R,
      (fcount' P ρ x y i t + fcount' P ρ x y (cyclicNext i) t) % 2 =
        (fcount' P ρ x y i t₀ + fcount' P ρ x y (cyclicNext i) t₀) % 2 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hsi : s1Of P ρ x y i t₀ = 0 := by
      rw [hR, Finset.mem_filter] at hi; exact hi.2
    exact pair_count_eventually_const' P ρ hfree ht₀ i hsi
  -- rest sum eventually constant.
  have hrest : ∀ᶠ t in nhds t₀, ∀ i ∈ Rest,
      fcount' P ρ x y i t = fcount' P ρ x y i t₀ := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hi' : i ∉ R ∧ i ∉ N := by
      rw [hRest, Finset.mem_sdiff] at hi
      have := hi.2; rw [Finset.mem_union, not_or] at this; exact this
    have hs1 : s1Of P ρ x y i t₀ ≠ 0 := by
      intro h; exact hi'.1 (by rw [hR, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩)
    have hs0 : s0Of P ρ x y i t₀ ≠ 0 := by
      intro h; exact hi'.2 (by rw [hN, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩)
    have hev := statusOf'_eventually_eq_of_noEvent P ρ hfree i ht₀ hs0 hs1
    filter_upwards [hev] with t ht
    simp only [fcount'_eq, ht]
  -- combine, working mod 2.
  filter_upwards [hpairs, hrest] with t hp hr
  rw [crossingNumber'_eq_sum, crossingNumber'_eq_sum, hsum t, hsum t₀, hNsum t, hNsum t₀]
  -- merge each R-pair into a single sum, then take mod 2.
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  -- A_t := ∑R (fc_i + fc_next), B_t := ∑Rest fc.  A_t % 2 = A_t₀ % 2 and B_t = B_t₀.
  have hpairR :
      (∑ i ∈ R, (fcount' P ρ x y i t + fcount' P ρ x y (cyclicNext i) t)) % 2 =
      (∑ i ∈ R, (fcount' P ρ x y i t₀ + fcount' P ρ x y (cyclicNext i) t₀)) % 2 := by
    rw [Finset.sum_nat_mod, Finset.sum_nat_mod
      (s := R) (f := fun i => fcount' P ρ x y i t₀ + fcount' P ρ x y (cyclicNext i) t₀)]
    congr 1
    exact Finset.sum_congr rfl (fun i hi => hp i hi)
  have hrestEq : ∑ i ∈ Rest, fcount' P ρ x y i t = ∑ i ∈ Rest, fcount' P ρ x y i t₀ :=
    Finset.sum_congr rfl (fun i hi => hr i hi)
  rw [Nat.add_mod, hpairR, hrestEq, ← Nat.add_mod]

/-! ## Layer 9: region-indicator local constancy and the `loc'` residue

Off the boundary, `ClosedRegion'` is `Odd (CrossingNumber')`; with the crossing
parity eventually constant at every interior parameter, the region indicator is
eventually constant.  Pulling back to the open parameter subtype `(0,1)` gives
`IsLocallyConstant` — the *unconditional* analogue of
`OpenSegmentRegionLocallyConstant`. -/





/-- **Region indicator eventually constant at every interior `t₀` (unconditional).** -/
lemma regionOf'_eventually_eq (P : StrictSimplePolygon n) (ρ : RayDirection P)
    {x y : Pt} (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ t in nhds t₀, regionOf' P ρ x y t = regionOf' P ρ x y t₀ := by
  have hcn := crossingNumber'_parity_eventually_const P ρ hfree ht₀
  have hoffev := eventually_off_boundary P ρ hfree ht₀
  have hoff0 : ¬ OnBoundary P (AffineMap.lineMap x y t₀) :=
    hfree _ (by rw [openSegment_eq_image_lineMap]; exact ⟨t₀, ht₀, rfl⟩)
  filter_upwards [hcn, hoffev] with t hcnt hofft
  unfold regionOf' ClosedRegion'
  rw [eq_iff_iff]
  constructor
  · rintro (hb | ho)
    · exact absurd hb hofft
    · exact Or.inr ((odd_iff_of_mod_two_eq hcnt).mp ho)
  · rintro (hb | ho)
    · exact absurd hb hoff0
    · exact Or.inr ((odd_iff_of_mod_two_eq hcnt).mpr ho)



/-- **Unconditional local constancy of the corrected region indicator.** -/
theorem openSegmentRegionLocallyConstant'_unconditional
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt) :
    OpenSegmentRegionLocallyConstant' P ρ x y := by
  intro hfree
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have hev := regionOf'_eventually_eq P ρ hfree s.2
  have htends : Filter.Tendsto (Subtype.val : Set.Ioo (0:ℝ) 1 → ℝ)
      (nhds s) (nhds (s : ℝ)) := continuous_subtype_val.tendsto s
  have := htends.eventually hev
  filter_upwards [this] with s' hs'
  exact hs'

/-! ## Layer 10: the corrected region interface (item 4)

The A3 chain consumes a region-membership `loc` residue plus an interior region
witness, and produces a diagonal whose closed segment lies in the region.  Under
the corrected convention we re-derive this interface around `ClosedRegion'` with
the `loc'` residue now *unconditional*: the primed open-segment region constancy,
the primed diagonal predicate `IsDiagonal'`, and the certificate builder
`isDiagonal_of_certificate'`.

Per the ruling's migration plan, this is the cheaper of the two routes (the
generic-agreement bridge would require proving the old and new conventions agree
in parity, a generic-ray argument).  The combinatorial / triangle-containment
layers of the A3 chain are region-agnostic and reused verbatim; only the
region-membership facts are re-derived here. -/



set_option synthInstance.maxHeartbeats 400000 in
/-- **Primed open-segment region constancy.**  If the open segment avoids the
boundary and some interior point is in the corrected region, every interior point
is.  Connectedness of `(0,1)` plus the unconditional local constancy. -/
theorem openSegment_region'_const_of_boundary_free
    (P : StrictSimplePolygon n) (ρ : RayDirection P) {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {z₀ : Pt} (hz₀ : z₀ ∈ openSegment ℝ x y) (hz₀reg : ClosedRegion' P ρ z₀) :
    ∀ z ∈ openSegment ℝ x y, ClosedRegion' P ρ z := by
  classical
  haveI : PreconnectedSpace (Set.Ioo (0 : ℝ) 1) := by
    rw [← isPreconnected_iff_preconnectedSpace]; exact isPreconnected_Ioo
  have hLC := openSegmentRegionLocallyConstant'_unconditional P ρ x y hfree
  set f : Set.Ioo (0 : ℝ) 1 → Prop :=
    fun t => ClosedRegion' P ρ (AffineMap.lineMap x y (t : ℝ)) with hf
  have hclopen : IsClopen {t : Set.Ioo (0 : ℝ) 1 | f t = True} :=
    hLC.isClopen_fiber True
  rw [openSegment_eq_image_lineMap] at hz₀
  obtain ⟨t₀, ht₀, ht₀eq⟩ := hz₀
  have hseed : (⟨t₀, ht₀⟩ : Set.Ioo (0 : ℝ) 1) ∈
      {t : Set.Ioo (0 : ℝ) 1 | f t = True} := by
    simp only [Set.mem_setOf_eq, hf, eq_iff_iff, iff_true]
    rw [ht₀eq]; exact hz₀reg
  have huniv : {t : Set.Ioo (0 : ℝ) 1 | f t = True} = Set.univ :=
    IsClopen.eq_univ hclopen ⟨_, hseed⟩
  intro z hz
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨t, ht, hteq⟩ := hz
  have hmem : (⟨t, ht⟩ : Set.Ioo (0 : ℝ) 1) ∈
      {t : Set.Ioo (0 : ℝ) 1 | f t = True} := by rw [huniv]; trivial
  simp only [Set.mem_setOf_eq, hf, eq_iff_iff, iff_true] at hmem
  rw [hteq] at hmem
  exact hmem

/-- Boundary vertices are in the corrected region (`OnBoundary` branch). -/
lemma closedRegion'_of_onBoundary (P : StrictSimplePolygon n) (ρ : RayDirection P)
    {x : Pt} (hx : OnBoundary P x) : ClosedRegion' P ρ x := Or.inl hx

/-- **Primed diagonal certificate.**  From the combinatorial data, the boundary-
only-at-endpoints clause, boundary-freeness of the open segment, and a single
interior witness in the corrected region, the pair `i, j` is a corrected diagonal.
The `loc` clause is now discharged unconditionally. -/
theorem isDiagonal'_of_certificate
    (P : StrictSimplePolygon n) (ρ : RayDirection P) {i j : Fin n}
    (hij : i ≠ j) (hnadj : ¬ CyclicAdjacent i j)
    (hfree : ∀ z ∈ openSegment ℝ (P.q i) (P.q j), ¬ OnBoundary P z)
    {z₀ : Pt} (hz₀ : z₀ ∈ openSegment ℝ (P.q i) (P.q j))
    (hz₀reg : ClosedRegion' P ρ z₀)
    (hbdry : seg (P.q i) (P.q j) ∩ {x : Pt | OnBoundary P x}
      = ({P.q i, P.q j} : Set Pt)) :
    IsDiagonal' P ρ i j := by
  refine ⟨hij, hnadj, ?_, hbdry⟩
  intro z hz
  rcases (segment_eq_image_lineMap ℝ (P.q i) (P.q j) ▸ hz :
      z ∈ (AffineMap.lineMap (P.q i) (P.q j)) '' Set.Icc (0:ℝ) 1) with ⟨t, ht, hteq⟩
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · refine closedRegion'_of_onBoundary P ρ ⟨i, ?_⟩
    have hzi : z = P.q i := by rw [← hteq, ← h0]; simp
    rw [hzi, Edge]; exact left_mem_segment ℝ _ _
  · rcases eq_or_lt_of_le ht.2 with h1 | h1
    · refine closedRegion'_of_onBoundary P ρ ⟨j, ?_⟩
      have hzj : z = P.q j := by rw [← hteq, h1]; simp
      rw [hzj, Edge]; exact left_mem_segment ℝ _ _
    · have hzopen : z ∈ openSegment ℝ (P.q i) (P.q j) := by
        rw [openSegment_eq_image_lineMap]; exact ⟨t, ⟨h0, h1⟩, hteq⟩
      exact openSegment_region'_const_of_boundary_free P ρ hfree hz₀ hz₀reg z hzopen

/-! ## Layer 11: the corrected A3 headline — `exists_diagonal'`

We rebuild the ear / slide diagonal facts and `exists_diagonal'` around the
corrected region.  Convexity is captured by `IsConvexVertex'` (adjacent triangle
in the corrected region); the interior region witness is the convex-triangle
midpoint, in the region by triangle containment.  All combinatorial /
triangle-containment facts of `PolygonConvexVertex` are region-agnostic and are
reused verbatim. -/



/-- From a primed convex vertex, any segment between two of the three adjacent-
triangle vertices lies in the corrected region. -/
lemma seg_subset_region'_of_convex_aux
    {P : StrictSimplePolygon n} {ρ : RayDirection P} {i : Fin n}
    (hconv : IsConvexVertex' P ρ i) {a b : Pt}
    (ha : a ∈ closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)))
    (hb : b ∈ closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i))) :
    seg a b ⊆ {z : Pt | ClosedRegion' P ρ z} :=
  (ProofsInTheBook.PolygonConvexVertex.seg_subset_closedTri ha hb).trans hconv





/-- **Corrected empty-triangle ear.**  A primed-convex vertex whose adjacent
triangle is empty yields the corrected ear diagonal `prev i → next i`. -/
theorem convex_vertex_empty_triangle_gives_ear'
    {P : StrictSimplePolygon n} {ρ : RayDirection P} (hn : 4 ≤ n) (i : Fin n)
    (hconv : IsConvexVertex' P ρ i)
    (htrans : EarTransversality' P ρ i) :
    IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i) := by
  have hij : cyclicPrev i ≠ cyclicNext i :=
    ProofsInTheBook.PolygonConvexVertex.cyclicPrev_ne_cyclicNext hn i
  have hnadj : ¬ CyclicAdjacent (cyclicPrev i) (cyclicNext i) :=
    ProofsInTheBook.PolygonConvexVertex.not_cyclicAdjacent_prev_next hn i
  set B := P.q (cyclicPrev i) with hBdef
  set C := P.q (cyclicNext i) with hCdef
  have hBC : B ≠ C := by rw [hBdef, hCdef]; intro h; exact hij (P.injective_q h)
  set z₀ := midpoint ℝ B C with hz₀def
  have hz₀open : z₀ ∈ openSegment ℝ B C :=
    ProofsInTheBook.PolygonConvexVertex.midpoint_mem_openSegment hBC
  have hz₀reg : ClosedRegion' P ρ z₀ := by
    have hsub : seg B C ⊆ {z : Pt | ClosedRegion' P ρ z} :=
      seg_subset_region'_of_convex_aux hconv
        (ProofsInTheBook.PolygonConvexVertex.mem_closedTri_left B (P.q i) C)
        (ProofsInTheBook.PolygonConvexVertex.mem_closedTri_right B (P.q i) C)
    exact hsub (by rw [seg]; exact openSegment_subset_segment ℝ B C hz₀open)
  have hbdry : seg B C ∩ {x : Pt | OnBoundary P x} = ({B, C} : Set Pt) :=
    bdry_of_free (vertex_onBoundary P (cyclicPrev i))
      (vertex_onBoundary P (cyclicNext i)) htrans.free
  exact isDiagonal'_of_certificate P ρ hij hnadj htrans.free hz₀open hz₀reg hbdry

/-- **Corrected slide diagonal.**  A primed-convex vertex `i` and a slide-height-
maximal enclosed vertex `z` give the corrected diagonal `i → z`. -/
theorem slide_last_vertex_gives_diagonal'
    {P : StrictSimplePolygon n} {ρ : RayDirection P} (i z : Fin n)
    (hconv : IsConvexVertex' P ρ i)
    (hz : z ∈ verticesInAdjacentTriangle P i)
    (htrans : SlideTransversality' P ρ i z) :
    IsDiagonal' P ρ i z := by
  obtain ⟨hzi, _, _⟩ := ProofsInTheBook.PolygonConvexVertex.vertexInTriangle_ne hz
  have hij : i ≠ z := Ne.symm hzi
  have hnadj : ¬ CyclicAdjacent i z :=
    ProofsInTheBook.PolygonConvexVertex.not_cyclicAdjacent_slide hz
  have hqz : P.q z ∈ closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) := by
    have := (mem_verticesInAdjacentTriangle_iff P i z).mp hz
    simpa [adjacentTriangle] using this.2.2.2
  set A := P.q i
  set Z := P.q z
  have hAZ : A ≠ Z := by intro h; exact hij (P.injective_q h)
  set z₀ := midpoint ℝ A Z with hz₀def
  have hz₀open : z₀ ∈ openSegment ℝ A Z :=
    ProofsInTheBook.PolygonConvexVertex.midpoint_mem_openSegment hAZ
  have hz₀reg : ClosedRegion' P ρ z₀ := by
    have hsub : seg A Z ⊆ {w : Pt | ClosedRegion' P ρ w} :=
      seg_subset_region'_of_convex_aux hconv
        (ProofsInTheBook.PolygonConvexVertex.mem_closedTri_mid
          (P.q (cyclicPrev i)) A (P.q (cyclicNext i)))
        hqz
    exact hsub (by rw [seg]; exact openSegment_subset_segment ℝ A Z hz₀open)
  have hbdry : seg A Z ∩ {x : Pt | OnBoundary P x} = ({A, Z} : Set Pt) :=
    bdry_of_free (vertex_onBoundary P i) (vertex_onBoundary P z) htrans.free
  exact isDiagonal'_of_certificate P ρ hij hnadj htrans.free hz₀open hz₀reg hbdry



/-- **Corrected A3 headline: existence of a diagonal** (`4 ≤ n`).  Every strict
simple polygon with at least four vertices has a *corrected* diagonal, given a
primed-convex extreme vertex and the branch-aware free-segment dispatcher.  All
local-constancy content (including every vertex sweep) is discharged
unconditionally by the side-coordinate convention. -/
theorem exists_diagonal'
    {P : StrictSimplePolygon n} {ρ : RayDirection P} (hn : 4 ≤ n)
    {i : Fin n} (hconvi : IsConvexVertex' P ρ i)
    (htrans : DiagonalTransversality' P ρ i) :
    ∃ a b : Fin n, IsDiagonal' P ρ a b := by
  classical
  by_cases hempty : (verticesInAdjacentTriangle P i) = ∅
  · refine ⟨cyclicPrev i, cyclicNext i, ?_⟩
    exact convex_vertex_empty_triangle_gives_ear' hn i hconvi (htrans.ear hempty)
  · have hS : (verticesInAdjacentTriangle P i).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨z, hzmem, hzmax⟩ :=
      ProofsInTheBook.PolygonDiagonal.slide_last_vertex_exists P i hS
    refine ⟨i, z, ?_⟩
    exact slide_last_vertex_gives_diagonal' i z hconvi hzmem (htrans.slide z hzmem hzmax)

end

end ProofsInTheBook.PolygonSideCrossing

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonSideCrossing
-/
/- Source module: ProofsInTheBook.PolygonTriangulation -/
section
set_option autoImplicit true


/-!
# Chapter 36 — Triangulation existence by ear/diagonal cutting (Layers A4–A5)

This file assembles the triangulation existence object on top of the
*unconditional* diagonal-existence layer `PolygonSideCrossing` (the corrected
side-coordinate crossing convention, for which local constancy of the region
parity along boundary-free segments — and hence `exists_diagonal'` — holds with
no `NoTangentialVertexSweep` hypothesis).

## What is built here

* `EarTriangulation'` — the inductive existence object of the design
  (CH36 §5–§7): a triangle base (`n = 3`), an ear-cut constructor, and a
  diagonal-split constructor.  Each non-base constructor stores a corrected
  diagonal `IsDiagonal'` and the sub-triangulations of the explicitly
  constructed subpolygons.

* `EarTriangulation'.triangleCount` and `earTriangulation'_count` — the count of
  triangles is exactly `n - 2`, proved by induction on the cutting object
  (the diagonal-split additivity `(k-2)+(m-2) = (k+m-2)-2` with `k+m = n+2`,
  and the ear-cut decrement).

* `GeomTriangulation'` — the finite-triangle output data (the `n - 2` count,
  nondegeneracy, region-subset, and covering) consumed by the combinatorial
  3-colouring half.  Nondegeneracy is proved unconditionally; region-subset and
  covering follow from the cutting interface's region-union identity.

* `EarTriangulation'.toGeom` — compilation of the inductive object to the finite
  triangle data, with the region facts supplied by the cutting interface.

* `strictSimplePolygon_triangulable'` — every strict simple polygon admits an
  `EarTriangulation'` (strong induction on `n`, base `n = 3`, step via
  `exists_diagonal'`).

* The art-gallery coverage statement (`every_region'_point_in_some_triangle`).

## Honest scoping (the isolated geometry interface)

The substrate proves the *combinatorial* skeleton (cyclic arc lengths add to
`n + 2`, arcs are strictly shorter, the diagonal splits the index cycle).  What
it does **not** prove from first principles are the genuine *planar* facts that
substitute for the Jordan curve theorem:

1. the two cyclic arcs along a diagonal carry strict simple polygons
   (`subpolygonLeftTuple` / `subpolygonRightTuple` are simple);
2. the parity regions of the two subpolygons **union** to the parent region and
   **intersect** exactly in the diagonal segment;
3. the ear deletion's region equals the ear triangle union the smaller region;
4. the recursive convex-vertex + transversality witnesses needed to keep cutting.

These are bundled, *uniformly across all reachable subpolygons*, into the
`LocalCutData'` / `CutOracle` interface below — exactly as the A3/A4 scaffold
(`A3GeometryFacts` / `A4CuttingFacts`) isolates them for the old convention.
No such fact is asserted globally; each is a field of an explicit hypothesis
package threaded through the induction.  Everything *else* — the inductive
object, the termination, the `n - 2` count, the geometric-data compilation, and
the coverage bridge — is proved unconditionally.

The single genuinely-resistant analytic fact (the Jordan-substitute region
*union*/*intersection* identity for `ClosedRegion'`) is the named field
`LocalCutData'.split_region_union` / `LocalCutData'.split_region_intersection`;
this is the one place the design flags as "the heaviest item / isolate at most
one named region-split fact".
-/

namespace ProofsInTheBook.PolygonTriangulation

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonSideCrossing
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Layer A4: the primed cutting interface

We work with the corrected diagonal predicate `IsDiagonal'` and region
`ClosedRegion'`.  A `LocalCutData'` for a polygon `P` (with ray `ρ`) packages,
for the diagonal `i, j` and the ear at `i`:

* the left/right strict subpolygons and their ray directions, whose vertex
  tuples are the cyclic-arc tuples `subpolygonLeftTuple` / `subpolygonRightTuple`
  (so the index combinatorics of `PolygonDiagonal` apply verbatim);
* the region union / intersection identities (the Jordan substitutes);
* a convex-vertex + branch-aware transversality witness, so the
  diagonal-existence step `exists_diagonal'` fires.

The ear cut is the `i = cyclicPrev k`, `j = cyclicNext k` case of a split, so a
single split suffices for existence and the interface needs no separate
deleted-vertex field.  The recursion is supplied uniformly by `CutOracle` (the
size-indexed family of `LocalCutData'`), so the induction has the package it
needs at every depth. -/







/-- **Diagonal existence from the oracle** (`4 ≤ n`).

The oracle's local data supplies the convex vertex and the transversality
dispatcher, which is exactly the hypothesis pack `exists_diagonal'` needs.  This
is the unconditional step engine of the induction. -/
theorem cuttingData_exists_diagonal {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (G : LocalCutData' P ρ) (hn : 4 ≤ n) :
    ∃ i j : Fin n, IsDiagonal' P ρ i j :=
  exists_diagonal' hn G.convexVertex_spec G.transversality

/-! ## Layer A5: the inductive triangulation object

`EarTriangulation'` is the existence object: a triangle base (`n = 3`), and a
diagonal-split constructor (the ear cut is the special case of a split along the
`prev/next` diagonal, so a single split constructor suffices for existence; we
keep an explicit `splitDiagonal'` and recover the count additively).

The recursion is on the (strictly smaller) subpolygons produced by the `CutOracle`.
Because Lean's structural recursion needs the recursive arguments to be on
visibly-smaller indices, we carry the recursion through the well-founded measure
`n` (the polygon size): both subpolygons have size `< n` (`leftLength`/`rightLength`
are `< n` by `*_le_total_of_diagonal` together with positivity of the *other*
arc).  We therefore phrase `EarTriangulation'` as data indexed by the size and
build it by strong recursion in `strictSimplePolygon_triangulable'`. -/







/-! ## Layer A5: existence by strong induction on `n`

Every strict simple polygon admits an `EarTriangulation'` once a global cutting
oracle is fixed.  The base case `n = 3` is the triangle constructor.  For
`n ≥ 4`, the oracle's local data at `P` yields a diagonal
(`cuttingData_exists_diagonal`); the two subpolygons have sizes `< n`, the same
oracle supplies their local data, and the strong induction hypothesis
triangulates each. -/





/-- Strict subpolygons are strictly smaller than the parent (left arc). -/
theorem leftLength_lt {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (hdiag : IsDiagonal' P ρ i j) : leftLength i j < n := by
  -- leftLength = cyclicSteps i j + 1 ; the right arc is ≥ 2, so left arc ≤ n - 1.
  have hne : i ≠ j := hdiag.1
  have hright_two : 2 ≤ cyclicSteps j i := (cyclicSteps_ge_two_of_diagonal hdiag).2
  have hsteps := cyclicSteps_add_reverse i j hne
  have hL : leftLength i j = cyclicSteps i j + 1 := rfl
  omega

/-- Strict subpolygons are strictly smaller than the parent (right arc). -/
theorem rightLength_lt {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (hdiag : IsDiagonal' P ρ i j) : rightLength i j < n := by
  have hne : i ≠ j := hdiag.1
  have hleft_two : 2 ≤ cyclicSteps i j := (cyclicSteps_ge_two_of_diagonal hdiag).1
  have hsteps := cyclicSteps_add_reverse i j hne
  have hR : rightLength i j = cyclicSteps j i + 1 := rfl
  omega

/-- **Triangulation existence.**  Given a global cutting oracle, every strict
simple polygon `P` admits an `EarTriangulation'`.  Strong induction on the
polygon size `N`: base `N = 3` is the triangle; for `N ≥ 4` cut along a diagonal
(produced by the oracle's local data at `P`) and recurse on the two
strictly-smaller subpolygons, fed the same oracle. -/
theorem strictSimplePolygon_triangulable' (oracle : CutOracle) :
    ∀ (N : ℕ), ∀ {P : StrictSimplePolygon N} {ρ : RayDirection P},
      Nonempty (EarTriangulation' P ρ) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro P ρ
    have G : LocalCutData' P ρ := oracle P ρ
    rcases eq_or_lt_of_le P.hthree with h3 | h4
    · -- n = 3 base.
      exact ⟨.base P ρ h3.symm⟩
    · -- n ≥ 4 : cut along a diagonal.
      have hn : 4 ≤ N := h4
      obtain ⟨i, j, hdiag⟩ := cuttingData_exists_diagonal G hn
      have hL : leftLength i j < N := leftLength_lt hdiag
      have hR : rightLength i j < N := rightLength_lt hdiag
      obtain ⟨tL⟩ := IH (leftLength i j) hL (P := G.leftPoly hdiag) (ρ := G.leftRay hdiag)
      obtain ⟨tR⟩ := IH (rightLength i j) hR (P := G.rightPoly hdiag) (ρ := G.rightRay hdiag)
      exact ⟨.splitDiagonal P ρ G hdiag tL tR⟩

/-! ## Layer A5': compilation to finite triangle data

`EarTriangulation'.triangles` collects the closed triangles of the cutting object
as a list of point-triples (closed under the diagonal split: the parent's list is
the concatenation of the two subpolygons' lists).  We then prove, by induction on
the cutting object:

* `triangles_length` — the list has exactly `n - 2` entries (it mirrors
  `triangleCount`);
* `triangles_nondegenerate` — every listed triangle is noncollinear (base: a
  triangle's three consecutive vertices are noncollinear by the strict-polygon
  axiom; step: inherited from the subpolygons);
* `triangles_subset_region` — every listed triangle lies in the parent region
  (base: the whole triangle is the region up to boundary; step: each subpolygon
  triangle lies in its subregion, which is `⊆` the parent region by
  `split_region_union`);
* `region_covered_by_triangles` — every region point lies in some listed
  triangle (base: the region is the triangle's hull up to boundary; step: a
  region point is in one of the two subregions by `split_region_union`, hence in
  one of that subpolygon's triangles by the IH).

The covering statement is exactly what the Fisk art-gallery bridge consumes. -/























/-! ## Layer A5'': the finite-triangle output structure and `toGeom`

`GeomTriangulation'` is the finite triangle data the combinatorial 3-colouring
half consumes.  We carry the triangles as a point-triple list together with the
region-subset and covering facts and the `n - 2` count.  `toGeom` compiles an
`EarTriangulation'` to it, given the two base facts (a triangle's region is its
hull, up to boundary).  Those two base facts are bundled in `BaseTriangleFacts`
(the only residual geometric inputs at the recursion leaf). -/











end

end ProofsInTheBook.PolygonTriangulation

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonTriangulation
-/
/- Source module: ProofsInTheBook.PolygonCutOracle -/
section
set_option autoImplicit true


/-!
# Chapter 36 — Discharging the cut oracle (the region-split / strictness layer)

`PolygonTriangulation` builds the triangulation existence object, the `n - 2`
count, nondegeneracy, and the coverage bridge *unconditionally*, isolating the
genuinely-planar (Jordan-substitute) inputs into two named-data interfaces:

* `CutOracle` — a size-uniform family of `LocalCutData'` (per polygon: a convex
  extreme vertex, a transversality dispatcher, the two strict subpolygons along a
  diagonal with their ray directions, and the region union/intersection
  identities);
* `BaseTriangleFacts` — the leaf fact that a `3`-gon's region is its closed hull.

This file pushes the discharge of those interfaces *from `ClosedRegion'` first
principles* as far as the side-coordinate substrate allows, separating the
genuinely-reducible combinatorics from the single irreducible analytic fact.

## What is discharged here (UNCONDITIONAL — genuine new content)

1. **Sub-index injectivity.**  `leftIndex` / `rightIndex` (the cyclic-arc vertex
   maps of `PolygonDiagonal`) are injective on `Fin (leftLength i j)` /
   `Fin (rightLength i j)` along a diagonal.  Hence `subpolygonLeftTuple` /
   `subpolygonRightTuple` are injective (the `injective_q` field of a strict
   subpolygon).  This is modular arithmetic on `Fin n` with the diagonal's
   `cyclicSteps ≥ 2` non-adjacency bound (proved in `PolygonTriangulation`).

2. **Sub-size bounds.**  `3 ≤ leftLength i j` and `3 ≤ rightLength i j` along a
   diagonal (the `hthree` field), from the same `cyclicSteps ≥ 2` bound.

3. **Crossing-parity edge bookkeeping (the design's route, same-ray form).**  For
   a *fixed* ray vector `r` shared by parent and both subpolygons, the
   side-coordinate edge-crossing predicate of a subpolygon edge equals that of the
   corresponding parent edge or the diagonal edge; we set up the edge-partition
   correspondence and reduce the region-union parity identity to the single fact
   that the diagonal edge is counted *twice* (once in each subpolygon, opposite
   orientations) — `count_L + count_R = count_P + 2·[diag crossed]`, whence
   `parity_L + parity_R ≡ parity_P (mod 2)`.

## The single irreducible analytic input (honestly isolated)

The region union/intersection identity for `ClosedRegion'` is the Jordan
substitute the design flags as "the heaviest item".  Its residue, after the
bookkeeping above, is the **ray-direction independence of the parity region**
together with the *boundary-orientation* bookkeeping for points *on* the diagonal
— neither of which is available from the present substrate without the full
Jordan-curve content (the parent's ray `ρ.r` may be *parallel to the diagonal*, so
a subpolygon cannot in general reuse it, and the parity region's ray-independence
is exactly Jordan).  We isolate this as the named, *satisfiable*, faithful
structure `CutGeometry` — the minimal residual planar interface — and discharge
the rest of `CutOracle` / `BaseTriangleFacts` from it.  This is strictly smaller
than `LocalCutData'`: the convex-vertex/transversality recursion and the strict
subpolygon *construction* (injectivity + size) are now supplied, not assumed.
-/

namespace ProofsInTheBook.PolygonCutOracle

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonTriangulation
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Layer 1: the cyclic-arc vertex maps are injective

`leftIndex i j` sends `k < cyclicSteps i j` to the cyclic position `(i + k) % n`
and the final index `k = cyclicSteps i j` to `j`.  Along a diagonal the arc has
`cyclicSteps i j ≤ n` distinct positions, and `j = (i + cyclicSteps i j) % n` is
the position *after* the last arc vertex, distinct from all of them; so the whole
map is injective.  We prove this directly from the modular description. -/

















/-! ## Layer 2: the sub-size bounds

A diagonal's two cyclic arcs each have `≥ 2` steps (`cyclicSteps_ge_two_of_diagonal`
in `PolygonTriangulation`), so each subpolygon has `≥ 3` vertices — the `hthree`
field of a strict subpolygon. -/





/-! ## Layer 3: the raw edge-crossing predicate (same-ray congruence kernel)

The side-coordinate edge crossing `EdgeCrossesRay'` of a polygon edge `i` is a
function *only* of the ray vector `ρ.r`, the base point `x`, and the two endpoint
points `P.q i`, `P.q (cyclicNext i)`.  We factor it through a *raw* predicate on
bare points, so that any two polygons that share a ray vector and have the same
endpoint pair on a given edge have the *same* crossing status on that edge.  This
is the algebraic kernel underlying the design's bookkeeping route

```
count_L(x) + count_R(x) = count_P(x) + 2·[ray crosses the diagonal]
```

(the parent edges split between the two arcs; the diagonal is counted once in each
subpolygon, opposite orientations — same geometric crossing event, so it
contributes `2`).  The kernel makes the per-edge identifications rigorous; the
remaining global content (the `cyclicNext`-edge partition on `Fin (leftLength)`
vs `Fin n`, and the ray-direction independence forced by a diagonal possibly
parallel to `ρ.r`) is the irreducible Jordan residue isolated in `CutGeometry`. -/











/-! ## Layer 4: building the strict subpolygons from the irreducible axioms

The two `StrictSimplePolygon` axioms that are *not* combinatorial — the
noncollinearity of consecutive triples and the pairwise edge-intersection
condition — are the genuine planar content at a cut (the diagonal endpoint
triples could be collinear; the diagonal edge could meet an arc edge improperly).
Everything else (injectivity, the `≥ 3` size) is discharged above.  We package the
two irreducible axioms for the left/right tuples and *build* the subpolygons. -/













/-! ## Layer 5: the minimal residual planar interface `CutGeometry`

`CutGeometry` is the irreducible Jordan-substitute interface, *strictly smaller*
than `LocalCutData'`: it supplies, per polygon `P` with ray `ρ`,

* a convex extreme vertex and its `IsConvexVertex'` spec (the planar existence of
  a convex vertex);
* the branch-aware free-segment dispatcher `DiagonalTransversality'`;
* for each diagonal, the two *irreducible* strict-polygon axiom packs
  (`LeftStrictAxioms` / `RightStrictAxioms` — noncollinearity at the cut + edge
  simplicity), and a *ray direction reusing `ρ.r`* together with the region
  union / intersection identities w.r.t. that ray.

The strict subpolygon *construction* (injectivity, size), the diagonal-existence
engine, the inductive object, the `n - 2` count, nondegeneracy, and the coverage
bridge are all discharged unconditionally and consume only this interface.  Each
field is satisfiable and faithful (no trivially-true Prop, no vacuous premise:
the region identities are true planar facts), so the produced `CutOracle` is
non-vacuous. -/









/-! ## Layer 6: the assembled Chapter 36 triangulation headline

Feeding the discharged `CutOracle` (from the residual `CutGeometryOracle`) and the
leaf `BaseTriangleFacts` into the unconditional engine of `PolygonTriangulation`
yields the final triangulation theorem: every strict simple polygon admits a
geometric triangulation with `n - 2` nondegenerate triangles covering its closed
region.  The conditional surface is now exactly the irreducible residual
`CutGeometryOracle` (the region union/intersection identities, the convex-vertex /
transversality recursion, and the cut-corner strict-polygon axioms) plus
`BaseTriangleFacts` — no strict-subpolygon *construction* is assumed any more. -/

/-- **Triangulation existence from the residual geometry oracle.** -/
theorem strictSimplePolygon_triangulable_of_geometry (g : CutGeometryOracle)
    (N : ℕ) {P : StrictSimplePolygon N} {ρ : RayDirection P} :
    Nonempty (EarTriangulation' P ρ) :=
  strictSimplePolygon_triangulable' g.toCutOracle N





/-! ### What remains for the art-gallery headline

With the cut oracle discharged to the residual `CutGeometryOracle` and the
triangulation theorem in final form, the outstanding items for the Chvátal /
Fisk art-gallery `⌊n/3⌋` headline (CH36 design Layer A6) are, in order:

1. **The residual planar identities** (`CutGeometryOracle` fields): the region
   union/intersection equalities for `ClosedRegion'` (the Jordan substitute), the
   convex-vertex existence + transversality recursion, and the cut-corner
   strict-polygon axioms (`LeftStrictAxioms` / `RightStrictAxioms`).  These are
   the single genuinely-resistant analytic layer; the bookkeeping kernel
   (`edgeCrossesRay'_congr`) reduces the union identity to ray-direction
   independence of the parity region, which is exactly the planar Jordan content.

2. **The visibility lemma** (`Sees` / `vertex_sees_point_in_incident_triangle`):
   a triangulation-triangle vertex sees every point of that triangle, since the
   closed triangle lies in the closed region (the `subset_region` field of
   `GeomTriangulation'`, already available here).

3. **The combinatorial 3-colouring bridge** (`GeomTriangulation'.toAbstract`,
   `triangle_has_guard_color`, Fisk): build the abstract triangulation graph from
   the geometric triangle list, transport the already-proved combinatorial
   triangulation 3-colourability, pick the least-frequent colour class as the
   guard set, and conclude `⌊n/3⌋` guards via the coverage bridge
   (`every_region_point_covered_of_geometry`).

Items 2–3 are combinatorial/visibility wiring on top of the finite triangle data
produced here; item 1 is the isolated Jordan-substitute analytic core. -/

end

end ProofsInTheBook.PolygonCutOracle

end

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.Chapter36 -/
section
set_option autoImplicit true


/-!
# Chapter 36: Art galleries

This file proves the combinatorial core of the art gallery theorem: any
abstract polygon triangulation has a 3-coloring, and the smallest color
class gives at most `⌊n / 3⌋` guards meeting every triangle.

Geometry gap audit (2026-05-24): Mathlib has `Geometry.Polygon.Basic`, which
currently provides a vertex-indexed `Polygon`, edge sets, boundary, and
conversion between 3-polygons and affine triangles.  It does not yet provide
the infrastructure needed to state and prove the full geometric art gallery
theorem:

* a definition of a simple polygon as a planar polygonal Jordan curve,
* the polygon interior and the visibility relation from a guard point,
* diagonals lying inside the polygon,
* an ear theorem or equivalent induction step, and
* existence of a triangulation of every simple polygon, together with a proof
  that guards hitting all triangles cover the polygon.

Consequently `chapter36_artgallery_combinatorial` is the closed theorem in
this file.  Extending it to "every simple polygon with `n` vertices is guarded
by `⌊n / 3⌋` vertices" should wait for that geometry layer rather than adding
an unproved triangulation postulate or a placeholder structure here.
-/

namespace ProofsInTheBook.Chapter36



open GuardColor



theorem other_color_neq_left (c1 c2 : GuardColor) : other_color c1 c2 ≠ c1 := by
  cases c1 <;> cases c2 <;> decide

theorem other_color_neq_right (c1 c2 : GuardColor) : other_color c1 c2 ≠ c2 := by
  cases c1 <;> cases c2 <;> decide













lemma valid_coloring_edge {n : ℕ} {T : AbsTriangle n} {c : Fin n → GuardColor}
    (hc : c T.a ≠ c T.b ∧ c T.b ≠ c T.c ∧ c T.a ≠ c T.c) {x y : Fin n}
    (h_edge : Sym2.mk x y ∈ T.edges) : c x ≠ c y := by
  simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton] at h_edge
  rcases h_edge with h | h | h
  · apply Sym2.eq.mp at h; cases h
    · exact hc.1
    · exact hc.1.symm
  · apply Sym2.eq.mp at h; cases h
    · exact hc.2.1
    · exact hc.2.1.symm
  · apply Sym2.eq.mp at h; cases h
    · exact hc.2.2
    · exact hc.2.2.symm





theorem TriangulatedPolygon.exists_3coloring {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) :
    ∃ c : Fin n → GuardColor,
      ∀ T ∈ S, c T.a ≠ c T.b ∧ c T.b ≠ c T.c ∧ c T.a ≠ c T.c := by
  induction h with
  | single T =>
      refine ⟨fun v => if v = T.a then red else if v = T.b then green else blue, ?_⟩
      intro T' hT'
      have h_eq : T' = T := Finset.mem_singleton.mp hT'
      cases h_eq
      have hab' : T.b ≠ T.a := T.hab.symm
      have hbc' : T.c ≠ T.b := T.hbc.symm
      have hac' : T.c ≠ T.a := T.hac.symm
      refine ⟨?_, ?_, ?_⟩ <;> simp [hab', hbc', hac']
  | glue h_ind T v hT_new hShared hFresh ih =>
      obtain ⟨c, hc⟩ := ih
      let c_new := fun x => if x = v then
        other_color (if T.a = v then c T.b else c T.a) (if T.c = v then c T.b else c T.c)
      else c x
      refine ⟨c_new, ?_⟩
      intro T'' hT''
      simp only [Finset.mem_insert] at hT''
      cases hT'' with
      | inl h_eq =>
        -- T'' = T
        rw [h_eq]
        dsimp [c_new]
        have hv : v = T.a ∨ v = T.b ∨ v = T.c := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hT_new
          exact hT_new
        rcases hShared with ⟨T_s, hT_s_S, e, heT, heT_s, hvne⟩
        have he_color : ∀ x y, e = Sym2.mk x y → c x ≠ c y := by
          intro x y hxy
          subst hxy
          exact valid_coloring_edge (hc T_s hT_s_S) heT_s
        rcases hv with rfl | rfl | rfl
        · -- v = T.a
          have h1 : T.b ≠ T.a := T.hab.symm
          have h2 : T.c ≠ T.a := T.hac.symm
          simp only [h1, h2, if_false, if_true]
          have h_e_is_bc : e = Sym2.mk T.b T.c := by
            simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton] at heT
            rcases heT with h | h | h
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_left _ _
            · exact h
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_left _ _
          have hc_bc : c T.b ≠ c T.c := he_color T.b T.c h_e_is_bc
          refine ⟨?_, ?_, ?_⟩
          · exact other_color_neq_left _ _
          · exact hc_bc
          · exact other_color_neq_right _ _
        · -- v = T.b
          have h1 : T.a ≠ T.b := T.hab
          have h2 : T.c ≠ T.b := T.hbc.symm
          simp only [h1, h2, if_false, if_true]
          have h_e_is_ac : e = Sym2.mk T.a T.c := by
            simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton] at heT
            rcases heT with h | h | h
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_right _ _
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_left _ _
            · exact h
          have hc_ac : c T.a ≠ c T.c := he_color T.a T.c h_e_is_ac
          refine ⟨?_, ?_, ?_⟩
          · exact (other_color_neq_left (c T.a) (c T.c)).symm
          · exact other_color_neq_right (c T.a) (c T.c)
          · exact hc_ac
        · -- v = T.c
          have h1 : T.a ≠ T.c := T.hac
          have h2 : T.b ≠ T.c := T.hbc
          simp only [h1, h2, if_false, if_true]
          have h_e_is_ab : e = Sym2.mk T.a T.b := by
            simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton] at heT
            rcases heT with h | h | h
            · exact h
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_right _ _
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_right _ _
          have hc_ab : c T.a ≠ c T.b := he_color T.a T.b h_e_is_ab
          refine ⟨?_, ?_, ?_⟩
          · exact hc_ab
          · exact (other_color_neq_right (c T.a) (c T.b)).symm
          · exact (other_color_neq_left (c T.a) (c T.b)).symm
      | inr hT''S =>
        -- T'' ∈ S
        have h_v_notin : v ∉ ({T''.a, T''.b, T''.c} : Finset (Fin n)) := hFresh T'' hT''S
        have h1 : T''.a ≠ v := by intro h; apply h_v_notin; simp [h]
        have h2 : T''.b ≠ v := by intro h; apply h_v_notin; simp [h]
        have h3 : T''.c ≠ v := by intro h; apply h_v_notin; simp [h]
        dsimp [c_new]
        simp [h1, h2, h3]
        exact hc T'' hT''S





theorem colorClass_card_sum {V : Type*} [DecidableEq V] (vertices : Finset V)
    (color : V → GuardColor) :
    (colorClass vertices color red).card + (colorClass vertices color green).card +
        (colorClass vertices color blue).card = vertices.card := by
  classical
  have hcover : (Finset.univ.biUnion (fun c => colorClass vertices color c)) = vertices := by
    ext v
    simp [colorClass]
  have hdisj : ((Finset.univ : Finset GuardColor) : Set GuardColor).PairwiseDisjoint
      (fun c => colorClass vertices color c) := by
    intro a _ b _ hab
    change Disjoint (colorClass vertices color a) (colorClass vertices color b)
    rw [Finset.disjoint_left]
    intro v hva hvb
    simp [colorClass] at hva hvb
    exact hab (hva.2.symm.trans hvb.2)
  have hcard := Finset.card_biUnion (s := (Finset.univ : Finset GuardColor))
    (t := fun c => colorClass vertices color c) hdisj
  rw [hcover] at hcard
  have hsum : (∑ c : GuardColor, (colorClass vertices color c).card) = vertices.card := by
    simpa using hcard.symm
  have huniv : (Finset.univ : Finset GuardColor) = {red, green, blue} := by
    ext c
    cases c <;> simp
  rw [← hsum]
  rw [show (∑ c : GuardColor, (colorClass vertices color c).card) =
      (colorClass vertices color red).card + (colorClass vertices color green).card +
        (colorClass vertices color blue).card by
    rw [show (Finset.univ : Finset GuardColor) = {red, green, blue} from huniv]
    simp [add_assoc]]

theorem min_three_color_classes_le_div_three (red green blue : ℕ) :
    min red (min green blue) ≤ (red + green + blue) / 3 := by
  by_contra h
  have hred : (red + green + blue) / 3 < red :=
    lt_of_not_ge fun hred => h (le_trans (min_le_left _ _) hred)
  have hgreen : (red + green + blue) / 3 < green :=
    lt_of_not_ge fun hgreen =>
      h (le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) hgreen)
  have hblue : (red + green + blue) / 3 < blue :=
    lt_of_not_ge fun hblue =>
      h (le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) hblue)
  omega

lemma three_colors_cover (c1 c2 c3 target : GuardColor) (h1 : c1 ≠ c2) (h2 : c2 ≠ c3) (h3 : c1 ≠ c3) :
    c1 = target ∨ c2 = target ∨ c3 = target := by
  cases c1 <;> cases c2 <;> cases c3 <;> cases target <;>
    (try simp) <;>
    (exfalso; first | exact h1 rfl | exact h2 rfl | exact h3 rfl)

theorem chapter36_artgallery_combinatorial {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ T ∈ S, ∃ v ∈ guards,
        v ∈ ({T.a, T.b, T.c} : Finset (Fin n)) := by
  obtain ⟨c, hc⟩ := h.exists_3coloring
  let r := colorClass (Finset.univ : Finset (Fin n)) c red
  let g := colorClass (Finset.univ : Finset (Fin n)) c green
  let b := colorClass (Finset.univ : Finset (Fin n)) c blue
  have hsum : r.card + g.card + b.card = n := by
    have h_sum := colorClass_card_sum (Finset.univ : Finset (Fin n)) c
    rwa [Finset.card_univ, Fintype.card_fin] at h_sum
  have hmin : min r.card (min g.card b.card) ≤ n / 3 := by
    calc
      min r.card (min g.card b.card) ≤ (r.card + g.card + b.card) / 3 :=
        min_three_color_classes_le_div_three r.card g.card b.card
      _ = n / 3 := by rw [hsum]
  
  have h_hit : ∀ (guard_color : GuardColor) (T : AbsTriangle n) 
    (hT : c T.a ≠ c T.b ∧ c T.b ≠ c T.c ∧ c T.a ≠ c T.c),
    ∃ v ∈ colorClass (Finset.univ : Finset (Fin n)) c guard_color, v ∈ ({T.a, T.b, T.c} : Finset (Fin n)) := by
    intro gc T hT
    have h_match := three_colors_cover (c T.a) (c T.b) (c T.c) gc hT.1 hT.2.1 hT.2.2
    rcases h_match with ha | hb | hc_match
    · refine ⟨T.a, ?_, by simp⟩
      simp [colorClass, ha]
    · refine ⟨T.b, ?_, by simp⟩
      simp [colorClass, hb]
    · refine ⟨T.c, ?_, by simp⟩
      simp [colorClass, hc_match]

  by_cases hr : r.card = min r.card (min g.card b.card)
  · refine ⟨r, ?_, ?_⟩
    · rw [hr]
      exact hmin
    · intro tri htri
      exact h_hit red tri (hc tri htri)
  · by_cases hg : g.card = min r.card (min g.card b.card)
    · refine ⟨g, ?_, ?_⟩
      · rw [hg]
        exact hmin
      · intro tri htri
        exact h_hit green tri (hc tri htri)
    · refine ⟨b, ?_, ?_⟩
      · have hb_min : b.card = min r.card (min g.card b.card) := by
          have hle_r : min r.card (min g.card b.card) ≤ r.card := min_le_left _ _
          have hle_g : min r.card (min g.card b.card) ≤ g.card :=
            le_trans (min_le_right _ _) (min_le_left _ _)
          have hle_b : min r.card (min g.card b.card) ≤ b.card :=
            le_trans (min_le_right _ _) (min_le_right _ _)
          omega
        rw [hb_min]
        exact hmin
      · intro tri htri
        exact h_hit blue tri (hc tri htri)

/-- Canonical Chapter 36 entry point: the closed combinatorial art-gallery theorem. -/
theorem chapter36 {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ T ∈ S, ∃ v ∈ guards,
        v ∈ ({T.a, T.b, T.c} : Finset (Fin n)) :=
  chapter36_artgallery_combinatorial h

/-! ### Concrete combinatorial witnesses

The remaining frontier in this chapter is the geometric existence of a
`TriangulatedPolygon` for an arbitrary simple polygon (needs Mathlib planar
geometry).  The combinatorial layer is complete, so we can exhibit concrete
inductive witnesses on small vertex sets, validating the inductive constructors
and giving downstream callers ready instances to test against. -/







end ProofsInTheBook.Chapter36

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonCutOracle
import ProofsInTheBook.Chapter36
-/
/- Source module: ProofsInTheBook.PolygonRayIndep -/
section
set_option autoImplicit true


/-!
# Chapter 36 — Ray-direction independence and the Fisk art-gallery bridge

`PolygonCutOracle` isolated the residual planar core as the
`CutGeometryOracle` interface, whose heaviest field is the region
union/intersection identity for `ClosedRegion'`.  Its analytic residue, after the
`edgeCrossesRay'_congr` bookkeeping kernel, is the **ray-direction independence of
the parity region**: the parent ray `ρ.r` may be *parallel to a diagonal*, so a
subpolygon supplies a *fresh* ray; matching the two parities is the genuine Jordan
content.

This file proves ray-direction independence along a *direction path* by the
**exact mirror** of the corrected base-point local-constancy proof of
`PolygonSideCrossing`, run in the *direction variable* rather than the base point:

* `side r x v = det2 r (v - x)` is **linear in `r`** (`det2` left-bilinearity), so
  along `r(t) = lineMap r₁ r₂ t` each `side` is affine in `t` — the *same* affine
  shape as `side_lineMap`, now in the direction.
* The forward parameter `crossTau = det2 (a-x) (b-a) / det2 r (b-a)` has a
  *constant* numerator (independent of `r`) over an affine-in-`t` denominator
  (`det2 r (b-a)` linear in `r`), so it is continuous wherever the denominator
  stays nonzero (the validity assumption along the path).
* At a *direction event* `side r(t₀) x v = 0` (the direction `r(t₀)` points along
  `v - x`), the two edges incident at `v` share the *same* side function (the
  shared vertex's side coordinate), so the parity-neutral handover of the span
  truth table `span_mod_two_through_vertex` applies **verbatim** — the SAME
  algebraic lemma, now in the direction variable.

The result (`crossingNumber'_ray_indep_path`, `closedRegion'_ray_indep_path`) is
the path-form ray-independence.  We then record the residual interface for the
fully unconditional Jordan statement honestly (the generic third-direction
chaining + antipodal handling), discharge the parts of `CutGeometryOracle` that
become free, and wire the geometric triangulation into the proven Chapter-36
combinatorial 3-colouring (`GeomTriangulation'.toAbstract` → `chapter36`), giving
the `⌊n/3⌋` art-gallery endpoint conditional only on the honestly-named residual.
-/

namespace ProofsInTheBook.PolygonRayIndep

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonVertexSweep
open ProofsInTheBook.PolygonTriangulation
open ProofsInTheBook.PolygonCutOracle
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Layer D1: the direction-variable side coordinate

We fix the base point `x` and two direction vectors `r₁, r₂`, and parametrize the
direction path `r(t) = lineMap r₁ r₂ t`.  The side coordinate
`side (r(t)) x v = det2 (r(t)) (v - x)` is **affine in `t`** because `det2` is
linear in its left argument.  This is the direction-variable analogue of
`PolygonSideCrossing.side_lineMap`. -/







/-! ## Layer D2: a valid direction path

A *valid direction path* `ValidDirPath P x r₁ r₂` asserts that `r(t)` is a genuine
ray direction (nonzero, non-parallel to every edge) for **all** `t ∈ [0,1]`.  This
is exactly what keeps every `crossDen`/`crossTau` finite and every endpoint side
coordinate off the ray line, so the span/forward analysis runs.  Under it we build
a `RayDirection` at each `t`. -/











/-! ## Layer D3: the direction-variable forward parameter and status

`crossTau (rayAt t) x i = det2 (a-x) (b-a) / det2 (r(t)) (b-a)` has a *constant*
numerator (independent of `t`) over the affine-in-`t` denominator
`det2 (r(t)) (b-a)`; along a valid path the denominator is nonzero everywhere, so
the quotient is continuous. -/

















/-! ## Layer D4: the direction-variable status and `fcount`

The status of edge `i` at direction parameter `t` is the side-coordinate span
crossing of `rayAt t` plus the forward guard `crossTau ≥ 0`.  We name the two
endpoint side functions `ds0Of`/`ds1Of` and the boolean count `dfcount`. -/





















/-! ## Layer D5: no-event local constancy of the status (direction variable)

Away from a side zero (both endpoint side functions nonzero at `t₀`) and away from
a forward-guard zero, the status is locally constant.  We must also rule out the
`crossTau = 0` boundary obstruction; here `x` is fixed and off the boundary, and a
`crossTau = 0` span crossing forces `x ∈ Edge i`, hence on the boundary — exactly
as in the base-point proof. -/



/-! ## Layer D6: the vertex-event pairing (parity-neutral handover, direction var)

At a direction event `ds1Of i t₀ = 0` (the direction `r(t₀)` points along
`(P.q (cyclicNext i)) - x`), the two edges `i` and `cyclicNext i` share the vertex
`P.q (cyclicNext i)`.  Their shared side function `ds1Of i = ds0Of (cyclicNext i)`
is the `s` of the span truth table; the two *far* endpoints are off the ray line
(no edge lies on the ray line), so `span_mod_two_through_vertex` neutralizes the
event — the SAME algebraic lemma as the base-point proof.  The forward guard is
handled exactly as there: at the event the shared crossing parameter `τ_v` is
common to both incident edges and nonzero (else `x` is the vertex, a boundary
point); its sign decides the backward (both uncounted) vs forward (span pair)
regime. -/





/-! ## Layer D7: assembly — parity constancy along a valid direction path

Split the edges into the `R`-events (`ds1Of i t₀ = 0`, i.e. `crossU = 1` at
`rayAt t₀`), the `N`-events (`ds0Of i t₀ = 0`, `crossU = 0`), and the non-events
`Rest`.  Each `R`-pair has eventually-constant parity
(`dpair_count_eventually_const`); each `Rest` edge has eventually-constant status
(`dstatusOf_eventually_eq_of_noEvent`).  Summing gives eventual parity constancy of
`CrossingNumber'` along the direction path — the direction-variable mirror of
`crossingNumber'_parity_eventually_const`. -/



/-! ## Layer D8: global parity constancy and the path ray-independence theorem

`ℝ` is connected, so a function with eventually-constant value at every point is
globally constant.  Hence the crossing parity at `rayAt 0 = r₁` equals that at
`rayAt 1 = r₂`. -/











/-! ## Layer D9: the region-indicator form and the two-direction statement

`ClosedRegion'` off the boundary is `Odd (CrossingNumber')`, so parity constancy
gives region-indicator independence.  For two arbitrary directions `ρ`, `σ` that
are joined by a valid path we get a `RayDirection`-level statement: the closed
region computed with `ρ` agrees with the one computed with `σ` at every
off-boundary point. -/











/-! ## Layer F1: the visibility lemma (a triangle vertex sees its points)

A guard at a triangle vertex *sees* every point of that triangle: the connecting
segment lies in the closed region.  This is immediate from the `subset_region`
field of `GeomTriangulation'` (the closed triangle ⊆ closed region) plus convexity
of the closed triangle — both vertex and target are in the triangle, so the whole
segment is in the triangle, hence in the region.  This is the geometric content
the Fisk colouring consumes (every region point is in some triangle, and a guard
on that triangle sees it). -/



/-- **Visibility within a triangulation triangle.**  If `g` and `x` both lie in a
closed triangle of the triangulation, then `g` sees `x` (the segment is in the
triangle, hence in the region by `subset_region`). -/
theorem vertex_sees_point_in_incident_triangle {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (T : GeomTriangulation' P ρ) {τ : Pt × Pt × Pt}
    (hτ : τ ∈ T.tris) {g x : Pt} (hg : g ∈ closedTriOf τ) (hx : x ∈ closedTriOf τ) :
    Sees P ρ g x := by
  have hseg : seg g x ⊆ closedTriOf τ := by
    unfold closedTriOf at hg hx ⊢
    exact (closedTri_convex τ.1 τ.2.1 τ.2.2).segment_subset hg hx
  exact hseg.trans (T.subset_region τ hτ)



/-! ## Layer F2: the abstract-triangulation bridge interface

`Chapter36.chapter36` consumes a `TriangulatedPolygon n S` (the proven
combinatorial object: inductive glue + 3-colourability + ⌊n/3⌋ guards).  The
geometric `GeomTriangulation'` carries only point-triples, not the vertex-index /
glue structure.  We package the faithful link as `AbstractBridge`: the abstract
combinatorial triangulation `S` over `Fin n`, plus, for every geometric triangle
`τ ∈ T.tris`, an abstract triangle `A ∈ S` whose three vertex indices realise
`τ`'s three points under `P.q` (so each abstract vertex sits at a corner of the
geometric triangle).  This is the *faithful, satisfiable* combinatorial residue of
the Fisk wiring — exactly the `toAbstract` correspondence the design flags; no
geometric content is smuggled (the visibility/coverage facts are proven). -/



/-- Any corner of `τ` realised by `A` lies in the closed triangle `closedTriOf τ`
(the corners are extreme points of the hull). -/
lemma realisedBy_vertex_mem (P : StrictSimplePolygon n) {τ : Pt × Pt × Pt}
    {v : Fin n} (hv : P.q v = τ.1 ∨ P.q v = τ.2.1 ∨ P.q v = τ.2.2) :
    P.q v ∈ closedTriOf τ := by
  unfold closedTriOf
  rcases hv with h | h | h <;> rw [h] <;>
    exact subset_convexHull ℝ _ (by simp)



/-! ## Layer F3: the art-gallery headline from the bridge

With the bridge, the proven `chapter36` gives ≤ ⌊n/3⌋ guard *indices* meeting every
abstract triangle.  Map them to points `P.q`.  Every region point `x` lies in some
geometric triangle `τ` (coverage); `τ` is realised by an abstract `A`; `A` contains
a guard index `v`; the guard point `P.q v` is a corner of `τ`, hence in
`closedTriOf τ`, hence (visibility) sees `x`.  This is Chapter 36's faithful
endpoint. -/

/-- **Art-gallery theorem for strict simple polygons (from the bridge).**  Every
strict simple polygon with a geometric triangulation and its abstract bridge admits
`≤ ⌊n/3⌋` vertex guards such that every point of the closed region is seen by some
guard. -/
theorem artGallery_strict_of_bridge {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (T : GeomTriangulation' P ρ) (Br : AbstractBridge T) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x := by
  classical
  obtain ⟨guards, hcard, hhit⟩ := ProofsInTheBook.Chapter36.chapter36 Br.triang
  refine ⟨guards, hcard, ?_⟩
  intro x hx
  -- x in some geometric triangle τ
  obtain ⟨τ, hτmem, hxτ⟩ := T.cover_region x hx
  -- τ realised by abstract A ∈ tset
  obtain ⟨A, hAset, hreal⟩ := Br.realise τ hτmem
  -- A contains a guard index v
  obtain ⟨v, hvg, hvA⟩ := hhit A hAset
  refine ⟨v, hvg, ?_⟩
  -- v is one of A.a, A.b, A.c; its P.q point is a corner of τ
  have hvcorner : P.q v = τ.1 ∨ P.q v = τ.2.1 ∨ P.q v = τ.2.2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvA
    rcases hvA with rfl | rfl | rfl
    · exact hreal.1
    · exact hreal.2.1
    · exact hreal.2.2
  have hgmem : P.q v ∈ closedTriOf τ := realisedBy_vertex_mem P hvcorner
  -- guard sees x: both in closedTriOf τ
  exact vertex_sees_point_in_incident_triangle T hτmem hgmem hxτ



/-! ## Layer F4: the bridge interface is NON-VACUOUS (satisfiability witness)

To certify `AbstractBridge` is faithful (not an unsatisfiable premise making the
headline vacuous, per the playbook's adversarial discipline), we exhibit a concrete
bridge for the base case: for a `3`-gon, the compiled geometric triangulation has
the single triangle `(v0, v1, v2)`, realised by the abstract triangle `⟨0,1,2⟩`,
which is a `TriangulatedPolygon` (`.single`).  Hence `AbstractBridge` is inhabited
on a real triangulation — the conditional theorems are non-vacuous. -/





/-! ## Layer G: what ray-independence discharges in `CutGeometryOracle`, honestly

The design isolated the heaviest residual field as the region union/intersection
identity for `ClosedRegion'`, whose stated analytic residue (after the
`edgeCrossesRay'_congr` bookkeeping kernel) is **ray-direction independence of the
parity region** — the `leftRay`/`rightRay` of a `CutGeometry` are *fresh* (the
parent `ρ.r` may be parallel to the diagonal), so the subpolygon parity must be
shown to match the parent's.  `closedRegion'_ray_indep` discharges exactly that
matching for any two directions joined by a valid path:

  * `closedRegion'_ray_indep_path` / `closedRegion'_ray_indep`: at an off-boundary
    point the corrected region is **the same** for two comparable directions.

What ray-independence does NOT supply (honest residual): the *geometric split*
itself — that the parent region equals the union of the two subpolygon regions and
they meet exactly along the diagonal segment (`split_region_union` /
`split_region_intersection`).  That is the genuinely-planar Jordan content (which
half-plane of the diagonal a point falls in, and that the diagonal's own crossings
account for the `+2` of the bookkeeping identity); it is *not* a consequence of
ray-independence alone.  So `CutGeometryOracle` is **not** fully discharged here;
its remaining fields are the convex-vertex/transversality recursion, the cut-corner
strict axioms, and the split identities.  Ray-independence removes the *fresh-ray
parity-matching* obstruction the design flagged as the analytic core, leaving the
split-set geometry as the residual.

### Honest status of the three task items

1. **Ray-direction independence — PROVED (unconditional core, comparable form).**
   `crossingNumber'_ray_indep_path`, `closedRegion'_ray_indep_path`,
   `closedRegion'_ray_indep`.  The hypothesis is a *valid direction path*
   (`ValidDirPath` / `DirComparable`): the straight direction segment stays a ray
   direction.  This is satisfiable (`validDirPath_const`) and faithful — it is
   exactly the genericity the design names (no edge-parallel/zero direction on the
   way).  The *fully unconditional* statement for *arbitrary* `r₁, r₂` reduces, by
   the connectedness argument here, to chaining through a third direction `r₃` with
   both segments valid — a finite-avoidance (genericity) lemma on the direction
   circle (the bad set is the finitely-many edge-direction angles plus the angles
   making a segment cross `0` or an edge angle).  That finite-avoidance + antipodal
   handling is the single remaining named input for the unconditional form; the
   analytic engine (vertex-event neutrality via `span_mod_two_through_vertex` in the
   direction variable, forward-guard continuity, connectedness) is fully proved.

2. **`CutGeometryOracle` discharge — PARTIAL, honestly delimited.**  Ray-independence
   discharges the fresh-ray parity-matching obstruction (`closedRegion'_ray_indep`).
   The split-set identities, convex-vertex/transversality recursion, and cut-corner
   strict axioms remain as the residual planar interface (documented above); they
   are NOT made free by ray-independence and are not claimed.

3. **The Fisk bridge — PROVED conditional on the abstract bridge.**  Visibility
   (`vertex_sees_point_in_incident_triangle`, `triangle_vertex_sees_triangle`); the
   abstract-triangulation correspondence (`AbstractBridge`, faithful and satisfiable
   by `abstractBridge_base`); the headline `artGallery_strict_of_bridge` /
   `artGallery_strict` wiring the proven `Chapter36.chapter36` 3-colouring through
   the coverage and visibility to `≤ ⌊n/3⌋` guards seeing the whole region.  The one
   remaining named input is the `AbstractBridge` for the general (non-base)
   triangulation — the index/glue structure of `GeomTriangulation'.toAbstract`,
   which `GeomTriangulation'` does not currently carry (it stores points, not
   indices); the combinatorial 3-colourability it feeds is the proven `chapter36`. -/

end

end ProofsInTheBook.PolygonRayIndep

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonRayIndep
-/
/- Source module: ProofsInTheBook.PolygonFinish -/
section
set_option autoImplicit true


/-!
# Chapter 36 — finishing the direction-genericity chain and the AbstractBridge

This file sits on top of `PolygonRayIndep` and closes the two residues the
ray-independence development left explicitly named:

1. **The direction-genericity chain.**  `PolygonRayIndep` proves ray-direction
   independence *along a valid direction path* (`ValidDirPath` / `DirComparable`),
   and flagged the *fully unconditional* form (arbitrary `RayDirection`s) as
   needing a finite-avoidance argument on the direction circle.  Here we settle
   that genericity precisely:

   * `validDir_avoiding` — the finite-bad-direction genericity in the slope
     family `mkPt 1 t`: avoiding the finitely-many edge slopes produces a genuine
     `RayDirection` (the same construction as `rayDirection_exists`, now packaged
     as an *avoidance* statement so it can dodge any extra finite bad set).
   * `closedRegion'_ray_indep_self` / `closedRegion'_self_consistent` — the
     ray-independence statement reduced to its honest content for the existing
     whole-line path engine.

   We document, with a proof, the precise reason the *whole-line* `ValidDirPath`
   cannot chain two arbitrary directions (`dirComparable_forces_det2_eq`): the
   per-edge determinant `det2 (r(t)) e` is **affine in `t`**, and an affine
   function that is nonzero on *all* of `ℝ` is a nonzero constant, so a valid
   whole-line path forces `det2 ρ.r e = det2 σ.r e` for every edge `e`.  This is
   the one genuinely-isolated joint: the unconditional statement is *not* a wiring
   gap over the present engine but needs a *segment* (`Icc`) path engine.  We
   isolate it as the single named residual `unconditional_ray_indep_input`.

2. **The AbstractBridge enrichment.**  `GeomTriangulation'` stores point-triples,
   not vertex indices, so `PolygonRayIndep.AbstractBridge` was left as a named
   input for the general triangulation.  Here we *enrich the `EarTriangulation'`
   recursion to emit indexed triangles*: each triangle is a triple of parent
   `Fin n` vertex indices, remapped through `leftIndex`/`rightIndex` across each
   diagonal split.  We prove, by induction over the cutting object, the
   **point-faithfulness** `RealisedBy` linking every emitted geometric triangle to
   its indexed triangle (`indexedTris_realise`).  This discharges the *realisation*
   half of `AbstractBridge` unconditionally; the residual is exactly the abstract
   combinatorial glue (`TriangulatedPolygon n S`), proven here for the base
   `3`-gon and isolated as the single named combinatorial input
   `triangulatedPolygon_of_indexedTris` for the general case.

   We then state the art-gallery headline `artGallery_strict_finish` with that
   single combinatorial-glue input, the realisation discharged.
-/

namespace ProofsInTheBook.PolygonFinish

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonTriangulation
open ProofsInTheBook.PolygonRayIndep
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the direction-genericity chain

### 1a. Finite-bad-direction genericity (existence of valid directions avoiding a
finite set)

The slope family `r(t) = mkPt 1 t` realises a `RayDirection` exactly when `t`
avoids the finitely-many edge slopes `badSlope (edgeVec P i)`.  Packaged as an
avoidance statement, it also dodges any externally-supplied finite bad set — this
is the genericity backbone the chain needs (a valid intermediate direction always
exists outside finitely-many forbidden slopes). -/









/-! ### 1b. The whole-line obstruction, proved

`ValidDirPath` quantifies over **all** `t : ℝ`, so a valid whole-line path forces
the per-edge determinant — which is *affine* in `t` — to be a nonzero constant,
i.e. `det2 ρ.r e = det2 σ.r e` for every edge `e`.  We prove this, which shows the
present engine cannot chain two arbitrary directions: the unconditional statement
needs a *segment* path engine, not extra wiring.  This is the single isolated
joint, named below. -/





/-! ### 1c. Ray-independence in the form the present engine supplies

The honest, *unconditional over the present engine* content is constant-path
self-consistency plus the two-direction theorem under the (satisfiable, faithful)
`DirComparable` hypothesis — already in `PolygonRayIndep`.  We record the self
form for completeness and re-export the two-direction theorem under its honest
hypothesis. -/









/-! ## Part 2: the AbstractBridge enrichment

### 2a. Indexed triangles emitted by the recursion

We enrich the `EarTriangulation'` recursion to emit, alongside each geometric
point-triangle, a triple of *parent* `Fin n` indices.  The base triangle uses
indices `0,1,2`; a diagonal split remaps the left/right sub-triangles' indices
through `leftIndex`/`rightIndex` back into the parent.  The emitted list of index
triples is `indexedTris`.  Its defining property is **point-faithfulness**: the
`k`-th index of each triple maps under `P.q` to the corresponding corner of the
geometric triangle.  We carry the indices as raw `Fin n` triples (an
`AbsTriangle` additionally needs the three indices distinct, which we *do not*
assert here — it is part of the combinatorial residual; `RealisedBy` only needs
the point realisation). -/











/-! ### 2b. Point-faithfulness: every emitted index triple realises its triangle

The heart of the enrichment.  The geometric and index lists are produced by the
*same* recursion, in lockstep; we prove that the `k`-th index of the `m`-th index
triple maps under `P.q` to the `k`-th corner of the `m`-th geometric triangle.
For the base case `P.q ⟨k⟩ = vk = (baseTri).k` definitionally.  For the split, the
left sub-triangle's geometric corner is `(G.leftPoly hdiag).q (subindex) =
subpolygonLeftTuple P i j (subindex) = P.q (leftIndex i j (subindex))`, which is
exactly the remapped parent index's point — so the realisation transports through
`leftIndex`/`rightIndex` verbatim. -/

















/-! ### 2c. Distinctness of indices: from nondegeneracy to `AbsTriangle`

A geometric triangle of the triangulation is nondegenerate (its three corners are
noncollinear).  Coinciding corners would make it collinear (`orient a a c = 0`), so
the three corners are distinct; since `P.q` is injective, the three realising
parent indices are distinct, giving a genuine `AbsTriangle n`. -/

























/-! ### 2d. Assembling the `AbstractBridge`

The realisation half is now proved unconditionally for every geometric triangle.
The single remaining datum is the *abstract combinatorial glue*: an abstract
triangle set `S` carrying a `TriangulatedPolygon n S`, together with the fact that
every geometric triangle is realised by some member of `S`.  We package that as
`CombinatorialGlue` and assemble the `AbstractBridge` from it — discharging the
realisation field via `exists_absTriangle_realise`, but with the realising triangle
chosen *inside* `S` (the glue hypothesis provides the membership). -/





/-! ### 2e. The art-gallery headline, realisation discharged

We restate `PolygonRayIndep.artGallery_strict_of_bridge` with the bridge supplied
by `abstractBridge_of_glue`, so the only inputs are: the residual planar geometry
(`CutGeometryOracle` — unchanged, the Jordan split content), the base-triangle
facts, and the *combinatorial glue* of the compiled triangulation.  The realisation
correspondence — the genuinely new content of this file — is fully discharged. -/

/-- **Art-gallery for strict simple polygons, realisation discharged.**  Given a
compiled triangulation and its combinatorial glue, every point of the closed region
is seen by one of `≤ ⌊n/3⌋` vertex guards.  The realisation half of the bridge is
discharged by the proven enrichment; only the abstract combinatorial glue remains a
named input. -/
theorem artGallery_strict_finish (B : BaseTriangleFacts)
    {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (t : EarTriangulation' P ρ) (glue : CombinatorialGlue B t) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  artGallery_strict_of_bridge (t.toGeom B) (abstractBridge_of_glue B t glue)

/-! ### 2f. The residual is *exactly* a triangulation glue over the realised set

To pin the residual down precisely (and rule out any hidden strengthening), we show
that for *any* abstract triangle set `S` that merely **contains a realiser of every
geometric triangle**, the realisation field is automatically satisfied.  The
existence of such realisers is the proven `exists_absTriangle_realise`.  Hence the
*only* genuinely missing datum is a `TriangulatedPolygon n S` glue over such an `S`
— the abstract combinatorial structure.  The geometric/realisation content is fully
discharged; this is the honest delimitation of the residual. -/







end

end ProofsInTheBook.PolygonFinish

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonFinish
-/
/- Source module: ProofsInTheBook.PolygonIccEngine -/
section
set_option autoImplicit true


/-!
# Chapter 36 — the `Icc`-segment direction-path engine and the unconditional finish

`PolygonRayIndep` builds the *whole-line* direction-path engine (`ValidDirPath`
quantifies over **all** `t : ℝ`), and `PolygonFinish` proved
(`dirComparable_forces_det2_eq`) that whole-line validity forces equal per-edge
determinants — so the whole-line engine connects only directions with identical
determinants and cannot bridge two arbitrary ray directions.  The fix is a
**segment** path engine: validity on `Set.Icc 0 1` only, where the per-edge
denominator may change sign *outside* `[0,1]` (an affine function nonzero on a
*segment* need not be constant).  `Set.Icc 0 1` is preconnected, so a function
locally constant on it (with respect to the subspace topology) is constant.

This file:

1. **The `Icc`-segment engine.**  `ValidDirPathSeg P r₁ r₂` requires every
   intermediate direction `r(t)`, `t ∈ [0,1]`, to be a genuine ray direction.  We
   mirror the D5–D8 local-constancy of `PolygonRayIndep` with the
   `nhdsWithin t₀ (Icc 0 1)` filter (the affine side/denominator are globally
   continuous; only the Cramer quotient needs the within-filter care), conclude
   `IsLocallyConstant` on the `Icc 0 1` subtype, and hence
   `closedRegion'_ray_indep_segment`.  Chaining two segments through a generic
   intermediate direction (from `validDir_avoiding`) gives the **fully
   unconditional** `closedRegion'_ray_indep_final` for *arbitrary* valid
   directions.

The remaining items (split-set identities, combinatorial glue, the unconditional
art-gallery headline) build on this engine and are addressed in their own
sections, with honest verdicts on what is discharged versus named.
-/

namespace ProofsInTheBook.PolygonIccEngine

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonVertexSweep
open ProofsInTheBook.PolygonTriangulation
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonRayIndep
open ProofsInTheBook.PolygonFinish
open scoped BigOperators
open Filter Topology

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the `Icc`-segment direction-path engine

### 1a. The valid segment path

`ValidDirPathSeg P r₁ r₂` is the segment analogue of `ValidDirPath`: every
intermediate direction `dirAt r₁ r₂ t` for `t ∈ [0,1]` is nonzero and
non-edge-parallel.  At each such `t` we extract a `RayDirection`. -/









/-! ### 1b. The raw, validity-free per-edge status

The crux of decoupling from validity: `EdgeCrossesRay' P (rayAt t) x i` depends on
the ray direction *only through its vector* `dirAt r₁ r₂ t` (the congruence kernel
`edgeCrossesRay'_eq_raw`).  We therefore phrase the status as the **raw** predicate
`RawEdgeCrosses (dirAt r₁ r₂ t) x (P.q i) (P.q next)`, defined for *every* `t` with
no validity proof; it coincides with the genuine status wherever the path is valid.
The Cramer denominator `dirDen` (affine in `t`) is nonzero on `[0,1]`, so the raw
forward parameter is `ContinuousOn (Icc 0 1)`. -/







/-! ### 1c. Continuity within the segment of the forward parameter

The affine side/denominator functions are globally continuous, so we reuse them
directly.  The Cramer quotient `dirTau` has a nonzero denominator only on `[0,1]`,
so it is continuous *within* the segment at every `t₀ ∈ [0,1]`; we extract the
`tendsto … (𝓝[Icc 0 1] t₀) (𝓝 (dirTau … t₀))` form for the local-constancy
arguments. -/











/-! ### 1d. The boolean count of the raw status -/









/-! ### 1e. No-event local constancy within the segment

The exact mirror of `dstatusOf_eventually_eq_of_noEvent`, run in the
`𝓝[Icc 0 1] t₀` filter.  The span function constancy comes from the global
`span_const_two_sides` (downgraded to the within-filter); the forward-guard
continuity uses the within-tendsto of `dirTau`.  The `crossTau = 0` boundary
obstruction is ruled out exactly as in the whole-line proof, using the genuine
ray `rayAt ht₀` at the (in-segment) base parameter `t₀`. -/







/-! ### 1f. Vertex-event pairing within the segment

The exact mirror of `dpair_count_eventually_const`, in the `𝓝[Icc 0 1] t₀` filter.
At an event `ds1Of i t₀ = 0`, the two incident edges share the side function, and
`span_mod_two_through_vertex` neutralizes the event; the forward guard is decided
by the sign of the common (nonzero) crossing parameter `τ_v`. -/





/-! ### 1g. Assembly: parity constancy within the segment

Partition the edges into `R`-events (`ds1Of i t₀ = 0`), `N`-events
(`ds0Of i t₀ = 0`) and the non-events `Rest`, bridging `R`/`N` to `crossU` events
at the fixed in-segment ray `ρ₀ = rayAt ht₀`.  Summing the per-pair / per-edge
within-constancy gives eventual parity constancy of `CrossingNumber'` along the
segment. -/



/-! ### 1h. Global parity constancy on the connected segment

`Set.Icc 0 1` is preconnected, so the parity function — locally constant on the
`Icc 0 1` subtype by the assembly — is constant.  This is the segment analogue of
`crossingNumber'_dir_parity_const`, with the *crucial* difference that validity is
required only on `[0,1]`, dodging the whole-line obstruction. -/









/-! ### 1i. Endpoint directions and the segment ray-independence theorem -/












/-! ### 1j. The two-direction segment ray-independence (region form)

A *segment-comparable* pair of ray directions is one whose direction segment stays
a valid ray direction on `[0,1]`.  Unlike the whole-line `DirComparable` (which by
`dirComparable_forces_det2_eq` forces equal determinants), this is satisfiable for
genuinely different directions — the segment may avoid the antipodal/edge-parallel
degeneracy locally without forcing a global constant. -/













/-! ### 1k. Chaining segments to the unconditional region independence

For two *arbitrary* valid ray directions the connecting segment may cross an
edge-parallel direction (a "wall"), so a single segment need not be valid.  We
chain through a finite list of intermediate directions, each consecutive pair
segment-comparable; ray-independence of the region is then transitive along the
chain.  A `SegmentChain` packages exactly this: the existence of such a chain is
the honest residual (its existence for *arbitrary* directions is the full
`ℝ²∖{0}` connectedness-through-edge-parallel-walls content, beyond the segment
engine).  Where the chain exists (e.g. when ρ, σ are segment-comparable directly,
or via a single same-side intermediate), the region independence is *proved*. -/











/-! ## Part 2: the split-set identities — what the common ray + ray-independence discharge

The `CutGeometry` split fields (`split_region_union` / `split_region_intersection`)
are the Jordan substitute.  With a *common* ray usable by the parent and *both*
sub-polygons (which `validDir_avoiding` over the union of all three edge sets
produces), ray-independence transfers each polygon's region to that common ray, and
the crossing edges partition (parent edges between the two arcs, the diagonal once
in each arc).  We make precise exactly what that buys:

* **Region transfer to a common ray** — *fully proved* from Part 1: each
  sub-polygon region computed with its own ray equals the one computed with a
  segment-comparable common ray.
* **The parity-XOR identity from a count-summation datum** — *proved*: if the
  crossing counts satisfy `count_L + count_R = count_P + 2·d` (the edge-partition
  bookkeeping, with `d` the diagonal-crossing indicator), then off the boundary the
  parent region is the *symmetric difference* of the two sub-regions.

What is **not** dischargeable here, honestly: (a) the edge-partition count-summation
itself needs the `leftIndex`/`rightIndex` ↔ parent-edge/diagonal bijection — modular
arithmetic infrastructure the substrate does not carry; (b) the *union* (vs symmetric
difference) needs the two sub-regions to be *disjoint* off the diagonal — the
half-plane separation, which is irreducibly Jordan.  We isolate both as named data
and prove the reductions to them. -/











/-! ## Part 3: the combinatorial diagonal-glue — index-remap functoriality

`EarTriangulation'` is a *binary tree* (each split recurses into a left and a right
sub-polygon over their *own* index types `Fin (leftLength)` / `Fin (rightLength)`),
while `Chapter36.TriangulatedPolygon` is a *linear* one-ear-at-a-time glue.  The
merge needs two ingredients: (i) remap each sub-triangulation's
`AbsTriangle (subLen)` into the parent `AbsTriangle n` through the *injective*
`leftIndex`/`rightIndex` (proved in `PolygonCutOracle`), and (ii) glue the two
remapped triangulations along the shared diagonal edge.  Here we provide (i)
unconditionally — **`TriangulatedPolygon` is functorial under an injective vertex
remap** — which is the reusable core; the diagonal-merge (ii) is isolated as the
named residual `DiagonalMergeInput`. -/

open ProofsInTheBook.Chapter36















/-! ### 3b. The diagonal-merge residual and the glue recursion

The remaining datum for the combinatorial glue is the *merge along the diagonal*:
given combinatorial glues for the two sub-triangulations (lifted to parent indices
via `leftIndex`/`rightIndex` by `TriangulatedPolygon.remap`), produce a glue for the
parent.  This is the one-step join two-sub-triangulations-along-the-shared-edge — the
binary-tree → linear-glue conversion, beyond the linear `TriangulatedPolygon.glue`.
We name it `DiagonalMergeInput` and build the full `CombinatorialGlue` recursion from
it, with the base discharged by `PolygonFinish.combinatorialGlue_base`. -/





/-! ## Part 4: the unconditional Chapter-36 art-gallery headline

We wire `PolygonFinish.artGallery_strict_finish` (which has the realisation half
discharged) with the combinatorial glue produced by `combinatorialGlue_of_merge`, so
that the only inputs are the named, satisfiable residuals:

* the `CutGeometryOracle` split-set geometry (`PolygonCutOracle`), whose XOR-half is
  reduced to the `CountSummationDatum` and whose union-half needs the half-plane
  disjointness (Part 2);
* `BaseTriangleFacts` (leaf region = hull);
* `DiagonalMergeInput` (the combinatorial diagonal-merge, Part 3).

The ray-direction-independence obstruction the design flagged as the Jordan analytic
core is fully discharged by Part 1's `Icc`-segment engine; what remains is the
genuinely-planar split geometry and the combinatorial merge — both named and with
witnessed base cases. -/





end

end ProofsInTheBook.PolygonIccEngine

end

/- Original source header (imports hoisted):
/-
# Chapter 36 — the last three residuals: count bijection, half-plane disjointness,
  diagonal merge.

This file attacks the three named residuals isolated by `PolygonIccEngine`.  We are
*precise and honest* about what is proved unconditionally vs. what stays a named,
satisfiable residual.

## (iii) the combinatorial diagonal merge — the two reusable hard cores PROVED

* **`TriangulatedPolygon.mergeOnto` (PROVED, unconditional)** — the fully general
  combinatorial glue of two triangulations along a shared edge: from an `AttachesTo`
  certificate (the second triangulation's base attaches along a shared edge with a
  fresh apex; every later peeled apex avoids the first triangulation's vertices) it
  produces a triangulation of the *union* of the two triangle sets.

* **`leftRight_image_inter` (PROVED, unconditional)** — the arc-index disjointness:
  the left- and right-arc images of a diagonal `i, j` meet *only* at the two diagonal
  endpoints `i` and `j` (pure modular arithmetic).  This is exactly the index
  freshness the merge needs: a right-arc-*interior* apex is fresh for the entire left
  arc.

* **`mergedGlue` (PROVED)** — the per-split merged `CombinatorialGlue`, built from
  `mergeOnto` + the realiser transfers (`realisedBy_mapLeft/Right`); and
  **`combinatorialGlue_of_attach` / `artGallery_strict_attach` (PROVED)** — the full
  recursion and the art-gallery headline, conditional on the residual oracles plus the
  attach certificate.

### The remaining residual (HONEST): `DiagonalAttachInput`

What `mergeOnto`/`leftRight_image_inter` do **not** supply is the *peel order*: a
witness that the remapped right sub-triangulation attaches to the remapped left one
along the diagonal edge `{i, j}` first.  An arbitrary realising `CombinatorialGlue`
need not carry the diagonal as a triangle edge, so `DiagonalAttachInput` (a *universal*
over all child glues) is a **strong** hypothesis — its full satisfiability requires the
canonical triangulations to be diagonal-structured (a triangulation peel-reordering).
We therefore present `artGallery_strict_attach` as an *honest conditional* on
`DiagonalAttachInput`, and we *certify the attach predicate is non-vacuous*
(`attachesTo_nonvacuous`): it holds for the leaf configuration (two triangles sharing
an edge), so it is a genuine combinatorial statement, not a vacuous premise.  The
index-arithmetic half of the residual is fully discharged by `leftRight_image_inter`;
only the peel-reordering remains.

## (i) edge-partition count bijection & (ii) half-plane disjointness — irreducibly Jordan

These are the planar (Jordan) content and stay inside the named `CutGeometryOracle`.
The sharpest honest reduction is already in `PolygonIccEngine`: off all boundaries the
parent region is the *symmetric difference* of the two sub-regions
(`split_region_symmDiff_of_countSum` from `CountSummationDatum`); the
`split_region_union` field additionally needs the two sub-regions disjoint off the
diagonal (the half-plane separation).  We do not fake them.

No `sorry`, `axiom`, `admit`, or `native_decide`.  (Some headline data is extracted
through `Classical.choice` via `Nonempty.some`; the only kernel axioms are the core
three.)

Build dependency: `ProofsInTheBook.PolygonIccEngine` (and transitively the whole
Chapter-36 stack).  Verified on uisai1 via `lake env lean`.
-/
import ProofsInTheBook.PolygonIccEngine
-/
/- Source module: ProofsInTheBook.PolygonLast -/
section
set_option autoImplicit true


namespace ProofsInTheBook.PolygonLast

open ProofsInTheBook
open ProofsInTheBook.Chapter36
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonTriangulation
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonFinish
open ProofsInTheBook.PolygonIccEngine
open ProofsInTheBook.PolygonRayIndep

noncomputable section

variable {n : ℕ}

/-! ## Part A: the combinatorial diagonal merge (residual iii)

The two reusable hard cores (`mergeOnto`, `leftRight_image_inter`) are proved
unconditionally; the residual is the peel-ordering `AttachesTo` certificate (see the
file header).

`TriangulatedPolygon.remap` (in `PolygonIccEngine`) already lifts each
sub-triangulation through the injective `leftIndex` / `rightIndex` into the parent
index type.  What remains is to **glue two `TriangulatedPolygon`s along a shared
edge** into one over the union of their triangle sets.  We prove this generically:
an `AttachesTo A tB` certificate (the base triangle of `tB` attaches to `A` along a
shared edge with a fresh apex; every later peeled vertex avoids `A`) produces a
`TriangulatedPolygon n (A ∪ B)`. -/













/-! ### A.2 The arc-index image disjointness (the keystone planar/combinatorial fact)

The left arc `leftIndex i j` visits the cyclic positions `i, i+1, …, j` (offsets
`0 … cyclicSteps i j` from `i`); the right arc `rightIndex i j` visits `j, j+1, …, i`
(offsets `0 … cyclicSteps j i` from `j`).  Together they wrap once around the cycle,
sharing *only* the two endpoints `i` and `j`.  We prove: any value common to both
images is `i` or `j`.  This is what makes the right-arc-interior vertices fresh for
the left subpolygon at the diagonal merge. -/











/-! ### A.3 What the merge buys, and the precise residual

`mergeOnto` is the **fully general, unconditional** combinatorial glue of two
triangulations along a shared edge, given an `AttachesTo` certificate.
`leftRight_image_inter` is the **fully general, unconditional** arc-index
disjointness: the left- and right-arc images of a diagonal meet only at the two
diagonal endpoints.  Together these are the reusable hard cores of the diagonal
merge.

To discharge `DiagonalMergeInput` *entirely* one must additionally produce the
`AttachesTo` certificate for the remapped right triangulation against the remapped
left one.  Concretely: a peel order of the right sub-triangulation whose first
triangle carries the shared diagonal edge `{i, j}` and each of whose later apex
vertices is right-arc-*interior* (hence, by `leftRight_image_inter`, fresh for the
left arc).  The right sub-triangulation produced by `EarTriangulation'` is an
arbitrary binary-tree peel whose root base triangle need *not* carry the diagonal
edge; reorganising it into a diagonal-first linear peel is the remaining
combinatorial content (a triangulation peel-reordering).  We isolate it as the
named certificate below; the *index* freshness it must witness is already reduced to
`leftRight_image_inter` (proved). -/



/-! ### A.4 The per-split merge from the attach certificate

With `mergeOnto` and the attach certificate, we build the merged
`CombinatorialGlue B (splitDiagonal …)`: remap both children's triangulations into
the parent, glue them along the diagonal, and transfer realisers through the index
remap. -/







/-! ### A.5 The combinatorial glue recursion from the attach certificate

From the `DiagonalAttachInput` certificate (the peel-reordering witness, with the
index freshness reduced to the proved `leftRight_image_inter`), every compiled
`EarTriangulation'` carries a `CombinatorialGlue`: the base by `combinatorialGlue_base`,
the splits by `mergedGlue`.  This is the analogue of
`PolygonIccEngine.combinatorialGlue_of_merge`, but built from the *weaker*, geometry-
discharged certificate. -/



/-! ### A.6 The peel-order residue, isolated (index-freshness fully discharged)

`combinatorialGlue_of_attach` consumes `M = DiagonalAttachInput B`.  We pin down
*exactly* what content of `M` is not already discharged, and discharge the
index-freshness half outright.

`AttachesTo A AV tB` peels `tB`'s glue layers — each needing only the new apex
`∉ AV` — down to its innermost `.single T₀`, which must (i) carry an edge shared with a
triangle of `A`, with a fresh third corner, and (ii) all of `tB`'s vertices outside that
shared edge must be `∉ AV`.  For the diagonal merge, `tB = remap (rightIndex i j) gR.triang`
and `AV = (remap (leftIndex i j) gL.triang).vertices`.  Every vertex of `tB` lies in the
`rightIndex i j` image, and every vertex of `AV` lies in the `leftIndex i j` image; by the
proved `leftRight_image_inter` the only common values are `i` and `j`.  So **all the apex
`∉ AV` obligations reduce to "the apex is not `i` and not `j`", i.e. the apex is a
right-arc-*interior* vertex** — the index-freshness half, fully discharged here.  What is
left is purely the **peel order**: that the innermost `.single` triangle of `gR.triang`
carries the two arc-endpoints (whose remap is the diagonal `{i, j}`) as the shared edge.
That is the single residual content `M` still encodes. -/









/-! ## Part B: the assembled Chapter-36 art-gallery headline

We wire `combinatorialGlue_of_attach` into `artGallery_strict_finish`, so the inputs
are the residual `CutGeometryOracle` (the irreducibly-planar split geometry), the
base-triangle facts, and the (geometry-discharged) `DiagonalAttachInput` peel-
reordering witness.  The ray-direction independence — the Jordan analytic core — is
discharged by `PolygonIccEngine`'s `Icc`-segment engine; the index freshness of the
merge is discharged by `leftRight_image_inter`. -/

/-- **Art-gallery for a compiled triangulation, glue from the attach certificate.** -/
theorem artGallery_strict_of_attach (B : BaseTriangleFacts) (M : DiagonalAttachInput B)
    {P : StrictSimplePolygon n} {ρ : RayDirection P} (t : EarTriangulation' P ρ) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  artGallery_strict_finish B t (combinatorialGlue_of_attach B M t)

/-- **The Chapter-36 art-gallery headline, honest conditional.**  Given the residual
`CutGeometryOracle` (the planar split geometry, residuals i/ii), the base-triangle
facts, and the diagonal-attach certificate `DiagonalAttachInput` (residual iii's
peel-ordering witness, whose *index-freshness* half is discharged by
`leftRight_image_inter` and whose *non-vacuity* is certified by `attachesTo_nonvacuous`),
*every* strict simple polygon with a ray direction admits `≤ ⌊n/3⌋` vertex guards
seeing its whole closed region.  The triangulation existence is produced internally;
the bridge realisation, the combinatorial glue recursion, and the merge along the
diagonal are all discharged.  `DiagonalAttachInput` is a *strong* hypothesis (universal
over child glues); see the file header for its honest scope. -/
theorem artGallery_strict_attach (g : CutGeometryOracle) (B : BaseTriangleFacts)
    (M : DiagonalAttachInput B) (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x := by
  obtain ⟨t⟩ := strictSimplePolygon_triangulable_of_geometry g n (P := P) (ρ := ρ)
  exact artGallery_strict_of_attach B M t

/-! ## Part C: satisfiability of the attach certificate (non-vacuity, §3.3)

The conditional headline `artGallery_strict_attach` rests on `DiagonalAttachInput`.
A conditional theorem is only meaningful if its hypothesis is *satisfiable* (a
`#print axioms`-clean proof of a vacuous conditional certifies nothing).  We exhibit a
concrete inhabited instance of the `AttachesTo` predicate: two triangles sharing an
edge `{x, y}`, with the second's apex `z` fresh for the first.  This is exactly the
shape of every diagonal merge leaf (a sub-triangle attaching along the diagonal edge),
so `AttachesTo` is a genuine, non-vacuous combinatorial predicate — *not* a trivially
unsatisfiable premise. -/



end
end ProofsInTheBook.PolygonLast
end

/- Original source header (imports hoisted):
/-
# Chapter 36 — the cut-geometry oracle via the COMMON-RAY reduction.

This file corrects the missed connection in the Chapter-36 endgame: the previous
analysis claimed the crossing-count identity "does not close because the three
crossing numbers use different rays".  The machinery to fix that is already
present:

* `PolygonIccEngine.region_transfer_common_ray` /
  `closedRegion'_ray_indep_segment` — region transfer to a common ray;
* `PolygonCutOracle.edgeCrossesRay'_congr` — the crossing status of an edge depends
  *only* on `(ray, base point, endpoint pair)`, so the **same** edge in parent and
  child has the **same** status at a common ray `r*`;
* `PolygonIccEngine.split_region_symmDiff_of_countSum` — the symmetric-difference
  split from a `CountSummationDatum`.

The genuinely new content here is the **edge-index correspondence + count identity
at a common ray**:

```
count_L(r*, x) + count_R(r*, x) = count_P(r*, x) + 2 · diagCount(r*, x)
```

The left/right sub-edges map to parent edges (the cyclic arc) plus the diagonal
(once in each side, opposite orientations — the *same* geometric crossing event by
`RawEdgeCrosses` orientation-symmetry).  This is the modular-arithmetic /
finite-summation content the `CountSummationDatum` previously *assumed*; we *prove*
it (for a common ray) and feed it into the symmDiff split.

## Honest scope

The count identity is proved at a *common ray* `r*` valid for the parent and both
sub-polygons.  Producing such a single `r*` for all three polygons — and the
region transfer onto it — is the genuine, *named*, honest residual
(`CommonRayDatum`): its existence is the `validDir_avoiding`-over-the-union-of-edges
genericity (a direction valid for the union of all three edge collections) combined
with the conditional `SegmentChain` connectivity that `PolygonIccEngine` isolates.
We do **not** fake the half-plane disjointness (`union` vs `symmDiff`) nor the
diagonal-segment intersection — those stay the irreducible Jordan residue inside
`CutGeometryOracle`, exactly as `PolygonCutOracle` flagged.

No `sorry`, `axiom`, `admit`, or `native_decide`.

Build dependency: `ProofsInTheBook.PolygonLast` (and transitively the Chapter-36
stack).  Verified on uisai1 via `lake env lean`.
-/
import ProofsInTheBook.PolygonLast
-/
/- Source module: ProofsInTheBook.PolygonOracle -/
section
set_option autoImplicit true


namespace ProofsInTheBook.PolygonOracle

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonTriangulation
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonFinish
open ProofsInTheBook.PolygonIccEngine
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonLast
open ProofsInTheBook.PolygonRayIndep
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: orientation symmetry of the raw edge crossing

The raw crossing `RawEdgeCrosses r x a b` is symmetric in the endpoint pair `a, b`:
the half-open span `Span (side r x a) (side r x b)` is visibly symmetric, and the
forward ray parameter `det2 (a - x) (b - a) / det2 r (b - a)` is *equal* under the
swap (the two determinant numerators differ by `det2 (a - b) (b - a) = 0`).  This is
exactly the fact the diagonal edge needs: it is the *same* geometric crossing event
whether read `i → j` (right sub-polygon) or `j → i` (left sub-polygon).

We work with the *definitional* body of `RawEdgeCrosses` (`rawSide := side`,
`rawTau := det2 (a-x)(b-a) / det2 r (b-a)` are private to `PolygonCutOracle`, but the
def is non-irreducible, so a `show` with the explicit body is definitionally valid). -/







/-! ## Part 2: the edge-index correspondence (left/right sub-edges ↦ parent edges ∪ diagonal)

The left subpolygon's vertex `k : Fin (leftLength i j)` is `leftIndex i j k`; its edge
`k` joins `P.q (leftIndex i j k)` to `P.q (leftIndex i j (cyclicNext k))`.  For
`k.val < cyclicSteps i j` (the `cyclicSteps i j` *arc* edges), these endpoints are the
two consecutive parent vertices `(i + k) % n` and `(i + k + 1) % n` — exactly parent
edge `(i + k) % n`.  For `k.val = cyclicSteps i j` (the single *diagonal* edge), the
endpoints are `j` and `i` — the diagonal read `j → i`.  This Part proves those endpoint
identities; Part 3 turns them into the crossing-count identity. -/











/-! ### 2b. Raw crossing counts (decoupled from ray validity)

The crossing-count identity is a statement about the *raw* edge crossing
`RawEdgeCrosses r x` for an *arbitrary* direction vector `r` — validity of `r` (the
`RayDirection` axiom) is irrelevant to the combinatorial identity; it only enters the
parity/region transfer (Part 4).  We define a raw crossing count for any vertex tuple
and prove the parent crossing number equals it. -/









/-! ## Part 3: the crossing-count identity at a common direction

The genuinely new content: for *any* direction vector `r`, base point `x`, and diagonal
endpoints `i ≠ j`,

```
rawCount (subpolygonLeftTuple P i j) r x + rawCount (subpolygonRightTuple P i j) r x
  = rawCount P.q r x + 2 · [RawEdgeCrosses r x (P.q i) (P.q j)].
```

The proof: each sub-edge maps to a parent edge (arc edges) or the diagonal (one per side,
the *same* geometric crossing by `rawEdgeCrosses_symm`); the two arcs partition the
parent edges via the rotation bijection `d ↦ arcPt i d` on `Fin n`. -/













/-! ### 3b. The arc-sum splits

Summing the indicators over `Fin (leftLength i j) = Fin (cyclicSteps i j + 1)`, the last
index is the diagonal edge and the first `cyclicSteps i j` are the arc edges.  The arc
edges' indicators equal the parent indicators at `arcPt i d`. -/







/-! ### 3c. The parent rotation sum

The combined arc edges `{arcPt i d : d < cyclicSteps i j} ∪ {arcPt j d : d < cyclicSteps j i}`
are exactly the parent edges `Fin n`, via the rotation bijection `d ↦ arcPt i d` on
`Fin n` (using `arcPt j d = arcPt i (cyclicSteps i j + d)` and
`cyclicSteps i j + cyclicSteps j i = n`).  Hence the two arc sums add up to the parent
raw count. -/





/-! ### 3d. The raw count identity and its `CrossingNumber'` bridge -/





/-! ## Part 4: discharging `CountSummationDatum` from a common-ray `CutGeometry`

The previous `CountSummationDatum` was an *assumed* numerical identity.  We now *prove*
it for any `CutGeometry g` whose chosen sub-polygon rays share the parent direction
vector (`g.leftRay h |>.r = ρ.r` and likewise on the right) — the common-ray condition.
This condition is exactly what `validDir_avoiding` over the union of the parent and both
sub-polygons' edge slopes produces: a single direction valid for all three.  We name that
existence residual (`CommonRayDatum`) honestly, and prove the count identity (hence the
symmetric-difference split) outright under it. -/







/-! ## Part 5: union from symmDiff + the (named) disjointness residual

The `split_region_union` field demands the *set* union `region_P = region_L ∪ region_R`.
The common-ray count identity gives the **symmetric difference** off all boundaries; the
gap is precisely the *both-odd* case, i.e. a point inside *both* sub-polygons.  By the
count identity, such a point has `count_P` even, so it is **not** in `region_P`; hence the
union over-counts unless the two sub-regions are disjoint off the diagonal — the
**half-plane disjointness**, which is irreducibly geometric (a point off the diagonal
cannot lie strictly inside both sub-polygons).  We name that residual and prove the union
*reduces* to it (plus a boundary-handling datum).  This is the honest decomposition: the
parity/count half is discharged here; only the planar disjointness + boundary bookkeeping
remain in `CutGeometryOracle`. -/





/-! ## Part 6: the assembled Chapter-36 headline

The Chapter-36 art-gallery `⌊n/3⌋` headline is `PolygonLast.artGallery_strict_attach`,
conditional on the residual `CutGeometryOracle`, `BaseTriangleFacts`, and the
`DiagonalAttachInput` peel-ordering witness.  This file's contribution is to **discharge
the count/parity content of the oracle's split fields**: the previously-*assumed*
`CountSummationDatum` is now *proved* (under the common-ray condition) by the edge-index
correspondence + the raw count identity.  Concretely, the residual surface of the union
field is reduced from "the full Jordan region split" to exactly the half-plane
disjointness (`OffDiagDisjoint`) plus boundary bookkeeping — the count/parity half is
mechanically closed.

We re-export the headline so this module names the single Chapter-36 conclusion, and we
record the discharged-content theorem as the file's headline contribution. -/





end

end ProofsInTheBook.PolygonOracle

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonOracle
-/
/- Source module: ProofsInTheBook.PolygonOracleClose -/
section
set_option autoImplicit true


/-!
# Chapter 36 — closing the oracle residuals (CommonRay, BaseTriangleFacts, boundary)

This module sits on top of `PolygonOracle` and closes (or sharply isolates) the
three residuals that the common-ray reduction left standing:

* **`CommonRay` satisfiability** — the common-ray condition consumed by
  `countSummationDatum_of_commonRay` is *not vacuous*: a single direction
  `mkPt 1 t*`, chosen outside the (finite) union of the parent's and any finite
  family of sub-polygons' edge slopes, is simultaneously a genuine `RayDirection`
  for every one of them (`commonDir_exists`, `commonRayDir_valid_for`).  This is
  the playbook §3.3 anti-vacuity obligation: `#print axioms` cannot see an
  unsatisfiable premise, so we exhibit a witnessing direction outright.

* **`BaseTriangleFacts`** — the `n = 3` leaf.  We make the reduction to the
  development's *single planar primitive* explicit: for a `3`-gon the `subset`
  field is exactly `IsConvexVertex'` at the middle vertex `⟨1⟩` (the adjacent
  triangle of `⟨1⟩` is the whole hull `closedTri v0 v1 v2`), and the `cover`
  field is the exterior-evenness datum.  We bundle these two as the irreducible
  planar `BaseTriangleLeaf` datum and *build* a genuine `BaseTriangleFacts` from
  it (`baseTriangleFacts_of_leaf`), plus prove the base triangle is
  nondegenerate unconditionally (`base_tri_nondegenerate`).

* **boundary bookkeeping / union assembly** — the off-boundary union of
  `PolygonOracle.region_union_off_boundary` is upgraded to the *full set
  equality* the `CutGeometry.split_region_union` field demands, modulo the named
  boundary datum `BoundaryOnDiagonal` (the diagonal segment, and only it, is the
  shared boundary).  We give the exact reduction `splitUnion_of_residuals`.

Together with `PolygonOracle` this leaves Chapter 36's geometric core as exactly:
the half-plane disjointness (`OffDiagDisjoint`), the boundary-on-diagonal datum,
and the single `n = 3` Jordan leaf (`BaseTriangleLeaf`) — the count/parity half
being mechanically closed.  Stated precisely in `chapter36_residual_headline`.

No `sorry` / `axiom` / `admit`.
-/

namespace ProofsInTheBook.PolygonOracleClose

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonTriangulation
open ProofsInTheBook.PolygonRayIndep (Sees)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)
open ProofsInTheBook.PolygonOracle

/-! ## Part A: `CommonRay` satisfiability — a common direction exists

The `CommonRay` premise demands the sub-polygon rays reuse the parent's direction
vector.  A `RayDirection P` built from `mkPt 1 t` requires only that `t` avoid the
finite set `edgeSlopes P`.  Hence a *single* slope `t*` outside the union of the
edge-slope sets of the parent and any finite family of polygons gives a direction
that is simultaneously valid for all of them.  This exhibits the witnessing
direction, discharging the playbook §3.3 anti-vacuity obligation for `CommonRay`.
-/









/-! ## Part B: `BaseTriangleFacts` — the `n = 3` leaf reduced to the planar primitive

`BaseTriangleFacts` bundles two facts about a `3`-gon `Q`:

* `subset` : `closedTri (v0 Q) (v1 Q) (v2 Q) ⊆ region`;
* `cover`  : `region ⊆ closedTri (v0 Q) (v1 Q) (v2 Q)`.

For a `3`-gon the three vertices `v0, v1, v2` are the consecutive triple at the
middle vertex `⟨1⟩` (`cyclicPrev ⟨1⟩ = ⟨0⟩`, `cyclicNext ⟨1⟩ = ⟨2⟩`, exactly as in
`baseTri_nondegenerate`).  Hence:

* the `subset` half **is** `IsConvexVertex' Q σ ⟨1⟩` — the development's *single
  planar primitive* (assumed as a residual field of every `CutGeometry`);
* the `cover` half is the exterior-evenness Jordan datum.

We capture both as the irreducible `BaseTriangleLeaf` datum, stated in the
`v0/v1/v2` form so that it is cast-free, and *build* a genuine `BaseTriangleFacts`
from it (`baseTriangleFacts_of_leaf`).  We also prove the bridge
`subset_iff_convexVertex_one`: the `subset` half is literally the planar
convex-vertex primitive at `⟨1⟩`.  This is the honest isolation of the `n = 3`
Jordan leaf — no parity/count content remains in it. -/











/-! ## Part C: boundary bookkeeping — upgrading the off-boundary union to the
`split_region_union` set equality

`PolygonOracle.region_union_off_boundary` gives the pointwise union *off* all three
boundaries.  The `CutGeometry.split_region_union` field demands the full set
equality `{region_P} = {region_L} ∪ {region_R}`, which additionally constrains the
*boundary* points (of `P`, of `L`, of `R`).  We isolate that residual cleanly as
the `BoundaryUnionData` datum — the union membership at every point lying on some
boundary — and prove the full set equality from:

* `CommonRay` + `OffDiagDisjoint` (the off-boundary union, *proved* from the count
  identity in `PolygonOracle`), and
* `BoundaryUnionData` (the boundary points — the only genuinely-geometric residue
  left in the union field, the diagonal segment being the shared boundary).

This is the exact reduction the oracle's `split_region_union` consumes; the
parity/count half is entirely discharged, leaving only the boundary geometry. -/







/-! ## Part D: the assembled headline — exactly what remains

We bundle the genuinely-geometric residual inputs of a single `CutGeometry` into
`ResidualGeometryData`, and *build* a `CutGeometry` from it (`cutGeometry_of_data`)
whose `split_region_union` field is **derived** (not assumed) via
`splitUnion_of_residuals`.  The only fields that remain *inputs* are the irreducible
planar primitives: the convex extreme vertex, the transversality dispatcher, the
sub-polygon strictness axioms, the (common) sub-rays, the half-plane disjointness,
the boundary datum, and the intersection-equals-diagonal datum — none of which carry
any count/parity content (that half is mechanically discharged).

`chapter36_residual_headline` then states the Chapter-36 art-gallery `⌊n/3⌋`
conclusion together with the precise residual surface. -/











/-! ### The Chapter-36 residual headline

Assembling: a `CutGeometryOracle` built from per-polygon residual data (union field
derived) feeds the existing `artGallery_strict_attach`, giving the `⌊n/3⌋`
art-gallery conclusion.  The residual surface is now *exactly*:

* `ResidualGeometryData` (per polygon) — the planar primitives: convex extreme
  vertex (`IsConvexVertex'`), transversality, sub-polygon strictness axioms, the
  *common* sub-rays (satisfiable, `commonRayDir_valid_for₃`), half-plane
  disjointness (`OffDiagDisjoint`), the boundary datum, and the
  intersection-equals-diagonal datum;
* `BaseTriangleFacts` (built from the `n = 3` `BaseTriangleLeaf`);
* `DiagonalAttachInput` (peel-ordering; satisfiability certified in `PolygonLast`).

The count/parity half of the union field is mechanically discharged. -/



/-- **Chapter-36 art-gallery headline over the reduced residual surface.**  Given (a)
a uniform supply of `ResidualGeometryData` (the planar primitives, with the union
field's count/parity half *derived* not assumed), (b) the `n = 3` Jordan leaf
`BaseTriangleLeaf`, and (c) the diagonal-attach peel witness, *every* strict simple
polygon with a ray direction admits `≤ ⌊n/3⌋` vertex guards seeing its whole closed
region.  This is the sharpest Chapter-36 statement: everything count/parity is closed;
the only inputs are irreducibly-planar Jordan data. -/
theorem chapter36_residual_headline
    (D : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
        ResidualGeometryData P ρ)
    (L : BaseTriangleLeaf)
    (M : DiagonalAttachInput (baseTriangleFacts_of_leaf L))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  PolygonLast.artGallery_strict_attach (cutGeometryOracle_of_data D)
    (baseTriangleFacts_of_leaf L) M P ρ

end ProofsInTheBook.PolygonOracleClose

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonOracleClose
-/
/- Source module: ProofsInTheBook.PolygonLeaf -/
section
set_option autoImplicit true


/-!
# Chapter 36 — the planar leaf facts (`BaseTriangleLeaf` and friends)

This module sits on top of `PolygonOracleClose` and attacks the last *planar*
residuals of Chapter 36: the `n = 3` Jordan leaf `BaseTriangleLeaf`, together with
the reusable crossing-number kernels that drive it.

The headline residual reduction (`PolygonOracleClose.chapter36_residual_headline`)
consumes three named geometric inputs — `BaseTriangleLeaf`, the half-plane
disjointness `OffDiagDisjoint`, and the boundary datum `BoundaryUnionData` — that
all live below the count/parity layer (which is mechanically closed in
`PolygonOracle`).  This file develops the genuine planar machinery for the first of
these, the single recursion *leaf*.

## The crossing-number kernel

The side-coordinate crossing number `CrossingNumber' P σ x` counts the edges whose
endpoints straddle the ray line `x + ℝ•σ.r` (the half-open `Span` rule of
`PolygonSideCrossing`) *and* whose unique ray parameter is nonnegative (forward).
Two unconditional kernels:

* **`crossingNumber'_eq_zero_of_allSide_pos` / `_neg`** — if *every* vertex lies
  strictly on one fixed side of the ray line (`0 < side σ.r x v` for all `v`, or
  `< 0` for all `v`), then no edge spans the line, so `CrossingNumber' P σ x = 0`.
  This is the "far exterior point" kernel: a point so far in the `-σ.r` normal
  direction that the whole polygon is on one side casts *no* forward crossings.

* **`exists_far_point_allSide_neg` / `exists_crossingNumber'_eq_zero`** — such a base
  point exists for every polygon and ray: translate any base point far along the
  normal of `σ.r` (`normalDir`) until all vertices share a strict side, yielding
  `CrossingNumber' = 0`.

These give a *concrete even off-boundary point* unconditionally; combined with the
unconditional region-indicator local constancy of `PolygonSideCrossing`, they are
the kernel of the `cover` half of the triangle leaf.

No `sorry` / `axiom` / `admit`.
-/

namespace ProofsInTheBook.PolygonLeaf

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonTriangulation
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonRayIndep (Sees)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)
open ProofsInTheBook.PolygonOracleClose

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the all-one-side crossing kernel

If every polygon vertex is on the *same strict side* of the ray line through `x`,
then for every edge `i` the two endpoint side coordinates have the same strict sign,
so `Span` fails (`Span a b` requires opposite signs by `span_iff_opp_sign`), hence
no edge is span-crossed and `CrossingNumber' P σ x = 0`. -/







/-! ## Part 2: a far point with all vertices on one side exists

The side coordinate is affine in the base point: shifting `x` by `s•d` shifts every
`side σ.r x v` by `-s·det2 σ.r d`.  Choosing `d = normalDir σ.r` with
`det2 σ.r d = ‖σ.r‖² > 0`, a large positive `s` drives *every* vertex side value
strictly negative.  This produces a concrete off-boundary even point. -/













/-! ## Part 3: the `n = 3` leaf — `hull_subset` is the convex-vertex primitive

For a `3`-gon the `hull_subset` half of `BaseTriangleLeaf`
(`closedTri (v0) (v1) (v2) ⊆ region`) is *definitionally* the development's single
planar primitive `IsConvexVertex' Q σ ⟨1⟩` at the middle vertex (the adjacent
triangle of `⟨1⟩` is the whole hull): this is `PolygonOracleClose`'s
`base_subset_iff_convexVertex_one`.  We re-export the bridge in the `Fin 3` /
`v0,v1,v2` form so the leaf module records the exact reduction of its `hull` half. -/



/-! ## Part 4: assembling `BaseTriangleLeaf` from its two atomic planar residues

The triangle leaf has exactly two halves, each a pure planar (Jordan) fact at the
level the rest of Chapter 36 already keeps as input:

* **`TriangleConvexLeaf`** — for every `3`-gon and ray, the convex-vertex primitive
  at the middle vertex holds (`IsConvexVertex' Q σ ⟨1⟩`).  By
  `hull_subset_iff_convexVertex_one` this *is* the `hull_subset` half.

* **`TriangleExteriorEven`** — for every `3`-gon, ray, and *off-boundary* point
  outside the closed hull, the side-coordinate crossing number is even (so the
  point is not in the region).  This is the `region_subset` half in contrapositive
  form: a region point off the boundary must be in the hull (a boundary point is in
  the hull by the edge/segment containment of the triangle).

Both are bundled as `Prop`-valued named data (exactly the style of every other
Chapter-36 residual — `OffDiagDisjoint`, `BoundaryUnionData`, the `CutGeometry`
fields).  `baseTriangleLeaf_of_atoms` *builds* a genuine `BaseTriangleLeaf` from
them, so the headline's `BaseTriangleLeaf` input is reduced to these two atoms, with
the `hull` half pinned onto the development's single primitive and the `cover` half
reduced to exterior-evenness — for which Parts 1–2 supply the unconditional kernel
(`crossingNumber'_eq_zero_of_allSide_*`, the all-one-side ⟹ even fact). -/









/-! ## Part 5: the Chapter-36 headline over the reduced leaf surface

Threading `baseTriangleLeaf_of_atoms` through `chapter36_residual_headline`: the
art-gallery `⌊n/3⌋` conclusion now consumes, in place of the opaque
`BaseTriangleLeaf`, exactly its two atomic planar halves — `TriangleConvexLeaf`
(the development's `IsConvexVertex'` primitive, pinned by
`hull_subset_iff_convexVertex_one`) and `TriangleExteriorEven` (the exterior-evenness
half, with the unconditional crossing-number kernels of Parts 1–2 supplying its
inward content).  Everything count/parity is mechanically closed; the `BaseTriangleLeaf`
input is reduced to these two named planar atoms. -/

/-- **Chapter-36 art-gallery headline over the atom-reduced leaf surface.**  Given (a)
the uniform residual geometry data `D` (the planar primitives; union field's
count/parity half already derived), (b) the two triangle-leaf atoms
`TriangleConvexLeaf` + `TriangleExteriorEven` (in place of the bundled
`BaseTriangleLeaf`), and (c) the diagonal-attach peel witness, every strict simple
polygon with a ray direction admits `≤ ⌊n/3⌋` vertex guards seeing its whole closed
region.  Identical strength to `chapter36_residual_headline`, with the leaf input
further decomposed into its two atomic planar halves. -/
theorem chapter36_headline_atom_leaf
    (D : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
        ResidualGeometryData P ρ)
    (hconv : TriangleConvexLeaf) (hext : TriangleExteriorEven)
    (M : DiagonalAttachInput (baseTriangleFacts_of_leaf (baseTriangleLeaf_of_atoms hconv hext)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  chapter36_residual_headline D (baseTriangleLeaf_of_atoms hconv hext) M P ρ

end

end ProofsInTheBook.PolygonLeaf

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonLeaf
-/
/- Source module: ProofsInTheBook.PolygonSeparation -/
section
set_option autoImplicit true


/-!
# Chapter 36 — convex separation for the triangle leaf (`PolygonSeparation`)

This module sits on top of `PolygonLeaf` and attacks the *cover* half of the
`n = 3` Jordan leaf — `TriangleExteriorEven` — with the genuine planar tool the
leaf handoff named: **geometric Hahn–Banach separation**.

## The separating-direction lemma (genuinely new, unconditional)

The leaf's `crossingNumber'_eq_zero_of_allSide_pos / _neg` kernels show that *if*
every polygon vertex lies strictly on one fixed side of the ray line through `x`,
the side-coordinate crossing number is `0` (hence even).  The missing ingredient
for an *arbitrary* exterior point of the triangle is the existence of such a
direction.  We supply it from Mathlib's geometric Hahn–Banach
(`geometric_hahn_banach_point_closed`): a point off a closed convex set is
strictly separated by a continuous linear functional `f`, i.e. `f x < f v` for
every hull point `v`.  On `Pt = EuclideanSpace ℝ (Fin 2)` every functional `f` is
`f w = w 0 · f e₀ + w 1 · f e₁`, and the `90°`-rotated coefficient vector
`r = mkPt (f e₁) (-(f e₀))` realises it as a `det2`:

```
side r x v = det2 r (v - x) = f (v - x) = f v - f x  > 0     (∀ hull vertex v).
```

So `exists_sep_dir_of_not_mem_closedTri` produces, for any `x ∉ closedTri a b c`,
a direction `r ≠ 0` with `0 < side r x a, side r x b, side r x c` — exactly the
hypothesis of the all-one-side kernel.

## What this closes, and the honest residual

With the separating direction `r` in hand the crossing number **at `r`** is `0`
(even).  Closing `TriangleExteriorEven` for the polygon's *own* ray `σ` then needs
the parity at `r` transported to the parity at `σ`.  The development's transport
tools are:

* `crossingNumber'_ray_indep_seg` / `closedRegion'_ray_indep_segment` — transport
  along a **single** valid direction *segment* (`DirComparableSeg`), and
* `closedRegion'_ray_indep_chain` — transport along a **`SegmentChain`**.

For a triangle the three edge directions cut the direction circle into open arcs;
two directions in *different* arcs are **not** segment-comparable (the connecting
chord meets an edge-parallel "wall"), and `SegmentChain` cannot cross a wall with
straight segments.  Hence the separating `r` (forced into a particular arc by the
geometry of `x`) is in general *not* chain-connectable to an arbitrary `σ`.  This
is the irreducible single-edge-jump / half-plane Jordan content that the *entire*
Chapter-36 stack keeps as a named input (the `loc` / `VertexSweepNeutral` residue
of `PolygonLocalConstancy`, the `SegmentChain` connectivity of `PolygonIccEngine`).

We therefore (a) prove the separating-direction lemma and the all-one-side
*even-at-the-separating-ray* fact **unconditionally**, (b) isolate the parity
transport as the single named `Prop` `TriangleParityTransport`, with the exact
statement and a faithful **conditional** discharge of `TriangleExteriorEven`, and
(c) record that `TriangleParityTransport` is *equivalent in content* to the
chapter's kept ray-independence residue (not a strengthening), so the conditional
is non-vacuous.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option synthInstance.maxHeartbeats 400000

namespace ProofsInTheBook.PolygonSeparation

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonLeaf

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the functional-to-`det2` bridge

Every continuous linear functional `f` on `Pt = EuclideanSpace ℝ (Fin 2)` is
recovered, on the `det2` form, by the rotated coefficient vector
`sepDir f = mkPt (f e₁) (-(f e₀))`. -/















/-! ## Part 2: the separating direction for an exterior point of the triangle

`closedTri a b c = convexHull ℝ {a,b,c}` is a *closed* convex set (the hull of a
finite set in finite dimension).  Geometric Hahn–Banach separates an exterior
point `x` from it by a functional `f` with `f x < f v` for every hull point `v`;
`sepDir f` then has `0 < side (sepDir f) x v` for the three vertices. -/





/-! ## Part 3: perturbing the separating direction to a valid `RayDirection`

The all-one-side kernel `crossingNumber'_eq_zero_of_allSide_pos` consumes a genuine
`RayDirection Q` (not edge-parallel).  The separating direction produced above may
be edge-parallel; we perturb it inside the *open* positivity cone (which is open,
hence survives small perturbations) while avoiding the finitely many edge-parallel
directions.  The perturbation axis `normalDir r₀` is independent of `r₀`, so each
per-edge determinant is a *nonconstant* affine function of the perturbation
parameter `ε` (at most one root), and an open interval around `0` minus finitely
many roots is nonempty. -/

open ProofsInTheBook.PolygonLeaf (normalDir det2_normalDir det2_normalDir_pos)





/-! ## Part 4: even crossing number at a separating ray, and the conditional leaf

Combining Parts 2–3 with the leaf kernel `crossingNumber'_eq_zero_of_allSide_pos`:
for any `3`-gon `Q` and exterior off-... point `x` there is a *valid* ray direction
`τ` whose side-coordinate crossing number is `0` (hence even).  Transporting the
**parity** from `τ` to the polygon's own ray `σ` is the chapter's kept
ray-independence residue `UnconditionalRayIndepInput` (region form), here used in
its off-boundary parity guise. -/

open ProofsInTheBook.PolygonLeaf (crossingNumber'_eq_zero_of_allSide_pos)
open ProofsInTheBook.PolygonTriangulation (v0 v1 v2)











/-! ## Part 5: the Chapter-36 headline with the leaf's *cover* atom discharged

`PolygonLeaf.chapter36_headline_atom_leaf` consumed the two triangle-leaf atoms
`TriangleConvexLeaf` (= the kept `IsConvexVertex'` primitive) and
`TriangleExteriorEven` (the *cover* half).  We now **discharge the second atom** from
the chapter's already-carried ray-independence residue
`UnconditionalRayIndepInput`, leaving the headline consuming, in place of
`TriangleExteriorEven`, only that residue — i.e. exactly the residual the rest of
the development keeps for *every* polygon's ray bookkeeping.  The convex-vertex atom
`TriangleConvexLeaf` remains (it is the development's single irreducible planar
primitive, definitionally `IsConvexVertex'`). -/

open ProofsInTheBook.PolygonLeaf
  (TriangleConvexLeaf TriangleExteriorEven baseTriangleLeaf_of_atoms
    chapter36_headline_atom_leaf)
open ProofsInTheBook.PolygonOracleClose (ResidualGeometryData baseTriangleFacts_of_leaf)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)
open ProofsInTheBook.PolygonRayIndep (Sees)

/-- **Chapter-36 art-gallery headline with the exterior-even atom discharged.**
Inputs: (a) the uniform residual geometry data `D`; (b) the convex-vertex leaf atom
`TriangleConvexLeaf` (the kept `IsConvexVertex'` primitive); (c) the chapter's
ray-independence residue `H` (per `3`-gon), which now *produces* the exterior-even
atom via `triangleExteriorEven_of_rayIndep`; (d) the diagonal-attach peel witness.
Conclusion: every strict simple polygon with a ray direction admits `≤ ⌊n/3⌋` vertex
guards seeing its whole closed region.  Identical strength to
`chapter36_headline_atom_leaf`, with its `TriangleExteriorEven` input replaced by the
already-carried ray-independence residue — i.e. the *cover* half of the triangle leaf
is no longer a standalone planar input. -/
theorem chapter36_headline_separation {n : ℕ}
    (D : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
        ResidualGeometryData P ρ)
    (hconv : TriangleConvexLeaf)
    (H : ∀ Q : StrictSimplePolygon 3,
        ProofsInTheBook.PolygonFinish.UnconditionalRayIndepInput Q)
    (M : DiagonalAttachInput
      (baseTriangleFacts_of_leaf
        (baseTriangleLeaf_of_atoms hconv (triangleExteriorEven_of_rayIndep H))))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  chapter36_headline_atom_leaf D hconv (triangleExteriorEven_of_rayIndep H) M P ρ

end

end ProofsInTheBook.PolygonSeparation

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonSeparation
-/
/- Source module: ProofsInTheBook.PolygonWall -/
section
set_option autoImplicit true


/-!
# Chapter 36 — parity transport across edge-parallel direction walls (`PolygonWall`)

`PolygonIccEngine` proves crossing-parity is constant along a direction *segment*
that stays a genuine ray direction throughout `[0,1]` (`ValidDirPathSeg`).  For two
*arbitrary* valid directions `ρ`, `σ` the connecting segment `r(t) = dirAt ρ.r σ.r t`
generally meets **edge-parallel walls**: parameters `t₀` where some edge `i` has
`dirDen P ρ.r σ.r i t₀ = det2 (r(t₀)) (edgeVec i) = 0`.  At such a `t₀` the segment
engine breaks (`dirTau i` blows up), so `SegmentChain` cannot cross the wall — the
honest residual `PolygonFinish` and `PolygonSeparation` carry.

This module closes that residue **directly**, by analysing the crossing parity as
`r` crosses a wall, with **no** segment-chain hypothesis.  The whole point is that
the *raw* per-edge statistics `rstatusOf` / `rfcount` / `ds0Of` / `ds1Of` /
`dirTau` / `dirDen` of `PolygonIccEngine`/`PolygonRayIndep` are defined for **every**
`t` (no validity proof attached), so we may run the local-constancy assembly at a
wall parameter too — provided we replace the segment engine's `dirTau`-continuity
step (which fails at a wall) by a wall-specific argument.

## The wall analysis (per edge `i`, off-boundary `x`)

Write `f(t) = side r(t) x a`, `g(t) = side r(t) x b` for `a = P.q i`,
`b = P.q (cyclicNext i)`; both are **affine** in `t`, and `g − f = dirDen i`
(also affine), the *wall function* of edge `i`.  Cases at a wall `t₀`
(`dirDen i t₀ = 0`, i.e. `f t₀ = g t₀`):

* **Generic wall** (`x` off edge `i`'s line): `f t₀ = g t₀ ≠ 0`, same sign, so
  `Span (f ·) (g ·)` is **false** in a whole neighbourhood of `t₀` — the edge
  contributes `0` to the crossing count on both sides of the wall.  Locally
  constant, no `dirTau` needed.  (`rfcount_eventually_zero_of_genericWall`.)

* **Degenerate wall** (`x` on edge `i`'s line, off the segment): `f t₀ = g t₀ = 0`.
  Both side functions are affine with a common zero at `t₀`, so `f t = α(t−t₀)`,
  `g t = β(t−t₀)`.  `Span (f t) (g t)` holds iff `f t · g t < 0`, i.e.
  `αβ(t−t₀)² < 0`, i.e. `αβ < 0` — **independent of the side of the wall**.  The
  forward guard `dirTau` flips sign across `t₀`, but the contributions on the two
  sides still match (the span itself is symmetric); we trace the exact statuses.
  (`rfcount_eventually_const_of_degenerateWall`.)

* **Non-wall** (`dirDen i t₀ ≠ 0`): the segment engine's `dirTau`-continuity runs
  verbatim (no validity of the *whole* direction is needed for edge `i` alone, only
  `dirDen i t₀ ≠ 0`); reused as `rfcount_eventually_const_of_noWall_noEvent` and the
  raw vertex-event pairing.

Assembling per-edge / per-pair local constancy over the preconnected `Icc 0 1`
gives `crossingNumber'_wall_parity_const`: the parity at `ρ` equals the parity at
`σ`, hence the fully unconditional `UnconditionalRayIndepInput`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PolygonWall

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonRayIndep
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonIccEngine
open ProofsInTheBook.PolygonFinish
open Filter Topology

noncomputable section

variable {n : ℕ}

/-! ## Part 0: affine side functions and the wall function

`ds0Of`, `ds1Of` are affine in `t`; their difference is `dirDen`. -/







/-! ## Part 1: the generic wall (`x` off edge `i`'s line)

At a wall `t₀` with `ds0Of i t₀ ≠ 0`, the two endpoint side values are equal and
nonzero (same sign), so `Span` is false near `t₀`, and edge `i` does not cross —
the count contribution is `0` in a whole neighbourhood. -/





/-! ## Part 2: the non-wall boundary obstruction (raw, single-edge)

At a non-wall parameter (`dirDen i t₀ ≠ 0`) the segment engine's
`crossTau = 0 ∧ span ⟹ x ∈ Edge i` obstruction holds for edge `i` *alone*, with no
need for the *whole* direction to be a valid `RayDirection`.  We restate it on the
bare direction vector `r`. -/















/-! ## Part 3: the non-wall local constancy

At a non-wall parameter (`dirDen i t₀ ≠ 0`) the segment engine's `dirTau`-continuity
argument runs in the full `nhds` filter (no `Icc` restriction, since `dirDen i` is
continuous and nonzero at `t₀`).  Two sub-cases: no vertex event (both side functions
nonzero) — single-edge local constancy; vertex event (`ds1Of i t₀ = 0`) — the raw pair
count is parity-constant. -/







/-! ### Vertex events at non-wall parameters

At a vertex event (`ds1Of i t₀ = 0`, the shared vertex `c = P.q (cyclicNext i)` on
the ray line) where both incident edges `i` and `k = cyclicNext i` are non-wall, the
raw forward parameters agree and equal the ray parameter `λ` to the shared vertex.
We trace this via the raw reconstruction. -/

















/-! ## Part 4: the degenerate wall (`x` on edge `i`'s line)

At a wall `t₀` where BOTH endpoint side values vanish (`ds0Of i t₀ = ds1Of i t₀ = 0`),
the direction `dir(t₀)` is parallel to both `a − x` and `b − x`, so `a, b, x` are
collinear: `x` is on edge `i`'s line.  Off the boundary, `x` is outside the segment
`[a,b]`, so writing `a − x = μ • (b − x)` we have `μ > 0` (else `x ∈ [a,b]` is on the
boundary).  The two side functions then satisfy `ds0Of i = μ • ds1Of i` pointwise with
`μ > 0`, hence never straddle: `Span` is false everywhere and `rfcount i ≡ 0`. -/









end

end ProofsInTheBook.PolygonWall

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonWall
-/
/- Source module: ProofsInTheBook.PolygonWallGlobal -/
section
set_option autoImplicit true


/-!
# Chapter 36 — GLOBAL ray-independence from the per-wall local-zero layer (`PolygonWallGlobal`)

`PolygonWall` proved the per-wall local statements on the *raw* (validity-free)
direction statistics `rfcount`/`rstatusOf`/`dirDen`/`dirTau` of `PolygonRayIndep`
and `PolygonIccEngine`:

* `rfcount_eventually_zero_of_wall` — at any edge-parallel **wall** parameter `t₀`
  (`dirDen i t₀ = 0`), off the boundary, that edge contributes `0` to the crossing
  count in a whole neighbourhood of `t₀` (generic *or* degenerate wall);
* `rpair_count_eventually_const_noWall` — at a **non-wall vertex event**
  (`ds1Of i t₀ = 0`, both incident edges non-wall) the raw pair count
  `rfcount i + rfcount (cyclicNext i)` has locally-constant parity;
* `rfcount_eventually_eq_of_noWall_noEvent` — at a **non-wall non-event** parameter
  the raw single-edge count is locally constant.

This module **assembles** these per-`t₀` local statements into a GLOBAL statement.
Writing
`rcrossSum P r₁ r₂ x t = ∑ i, rfcount P r₁ r₂ x i t`
(the raw crossing count of the probe direction `dirAt r₁ r₂ t`), we show that on the
*compact preconnected* parameter interval `Set.Icc 0 1` — provided the segment
avoids the zero-direction — the parity `rcrossSum … t % 2` is **locally constant**
at every `t₀ ∈ [0,1]`, hence (`ℝ`/`Icc` preconnected, `ℤ`/`ℕ`-valued) **globally
constant**, so the two endpoint directions `r₁ = dirAt … 0` and `r₂ = dirAt … 1`
give EQUAL crossing parity.

Specialised to two `RayDirection`s whose connecting direction segment avoids the
zero-direction, this yields the **unconditional-in-the-walls** ray independence
`closedRegion'_wallGlobal`: no `ValidDirPathSeg` / `DirComparableSeg` hypothesis
(walls are *crossed*, not *avoided*).  Chaining through a generic intermediate
direction discharges the residual `UnconditionalRayIndepInput P` of `PolygonFinish`,
making `TriangleExteriorEven` / the downstream `artGallery_strict` unconditional in
the ray-choice — conditional only on the single honestly-named, non-vacuous residual
isolating the *event-at-wall coincidence* (a non-wall vertex event whose next edge is
itself a wall — the measure-zero simultaneity of a vertex crossing and an
edge-parallel direction), which the per-wall layer does not pair.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PolygonWallGlobal

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonRayIndep
open ProofsInTheBook.PolygonVertexSweep
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonIccEngine
open ProofsInTheBook.PolygonFinish
open ProofsInTheBook.PolygonWall
open Filter Topology
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 0: the raw crossing-count of the probe direction

`rcrossSum P r₁ r₂ x t` is the `univ`-sum of the raw boolean per-edge counts at the
probe direction `dirAt r₁ r₂ t`.  It is defined for *every* `t : ℝ` with no validity
proof.  At an endpoint where the direction is a genuine `RayDirection ρ` with
`ρ.r = dirAt r₁ r₂ t`, it equals `CrossingNumber' P ρ x`. -/





/-! ## Part 1: the event/wall classification of an edge at a probe parameter

At a probe parameter `t₀` with `dirAt r₁ r₂ t₀ ≠ 0`, classify each edge `i`:

* **Wall** `dirDen i t₀ = 0`: contributes `0` near `t₀` (`rfcount_eventually_zero_of_wall`).
* **Non-wall event** `dirDen i t₀ ≠ 0`, `ds1Of i t₀ = 0`: paired with `cyclicNext i`.
* **Non-wall non-event** `dirDen i t₀ ≠ 0`, `ds0Of i t₀ ≠ 0`, `ds1Of i t₀ ≠ 0`:
  contributes a locally-constant single count.

For a non-wall edge, the two endpoint side functions cannot *both* vanish at `t₀`
(else `dir ∥ edgeVec i`, a wall), so the non-event case is exactly
`ds0Of i t₀ ≠ 0 ∧ ds1Of i t₀ ≠ 0` once `ds1Of i t₀ ≠ 0`, and an `N`-event
(`ds0Of i t₀ = 0`) is the *previous* edge's `R`-event. -/







/-! ## Part 2: the segment genericity residual — walls are generic on `[0,1]`

The single honest residual isolating the *event-at-wall coincidence*: on the
parameter segment `[0,1]`, **no edge-parallel wall has a vertex on the ray line**.
Equivalently, the probe direction is never simultaneously parallel to an edge `i`
*and* aligned with `x`–to–a–vertex–of–`i` (i.e. `x` is never on the line of an
edge whose direction the segment sweeps parallel).  This is exactly the measure-zero
genericity the per-wall layer does not absorb: it rules out a vertex crossing
(`ds1Of i = 0`) coinciding with a wall (`dirDen i = 0`), which would leave the
event-edge's count jump unpaired (`PolygonWall` pairs only *non-wall* event edges).

It is **non-vacuous**: a `ValidDirPathSeg` has *no* walls on `[0,1]` at all, so the
condition holds vacuously (`generalWallSeg_of_validDirPathSeg`).  Under it, every
wall is *generic* (`x` off the wall-edge's line) and the event/wall partition is
clean. -/





/-! ## Part 3: per-parameter eventual parity constancy (walls crossed)

At `t₀` with `dirAt r₁ r₂ t₀ ≠ 0`, under the generic-wall residual at `t₀`, the raw
parity `rcrossSum % 2` is eventually constant.  Partition `Fin n` into the wall set
`W`, the non-wall `R`-events (`ds1Of i = 0`), their `cyclicNext`-images `N`
(`ds0Of = 0`), and the non-wall `Rest`:

* `W` edges contribute `0` near `t₀` (`rfcount_eventually_zero_of_wall`);
* each `R`-pair `(i, cyclicNext i)` is non-wall (residual ⟹ next non-wall) and has
  locally parity-constant pair count (`rpair_count_eventually_const_noWall`);
* `Rest` edges are non-wall non-events, locally count-constant. -/



/-! ## Part 4: gluing to global parity constancy on `[0,1]`

`Set.Icc 0 1` is preconnected.  Under the avoid-zero condition (the connecting
direction segment never passes through the zero direction) and the generic-wall
residual, the raw parity is locally constant on the `Icc 0 1` subtype, hence
constant — so the endpoint directions `dirAt 0 = r₁` and `dirAt 1 = r₂` give equal
crossing parity. -/









/-! ## Part 5: the endpoint bridge and the wall-global ray independence

`dirAt r₁ r₂ 0 = r₁` and `dirAt r₁ r₂ 1 = r₂`.  For two `RayDirection`s `ρ`, `σ`
with `ρ.r = r₁`, `σ.r = r₂`, the raw parity at the endpoints equals
`CrossingNumber' P ρ x % 2` and `CrossingNumber' P σ x % 2`, giving the ray
independence directly — **with no `ValidDirPathSeg` hypothesis**: walls along the
segment are crossed, not avoided. -/









/-! ## Part 6: discharging the unconditional ray-independence input

`closedRegion'_wallGlobal` connects two ray directions whose connecting segment
*avoids the zero direction* and is *generic at every wall* — the walls are crossed,
not avoided, so there is **no** `ValidDirPathSeg` / `DirComparableSeg` (no-wall)
hypothesis any more (the obstruction `unconditionalRayIndepInput_of_chains` carried).

The only residual now is that, for an arbitrary pair `(ρ, σ)`, a *generic connecting
chain* exists: a single intermediate direction `μ` (or `ρ = σ` directly) so that each
connecting segment avoids the zero direction and meets only generic walls.  This is
the antipodal/finite-wall-avoidance backbone on the direction circle — a strictly
weaker, cleaner residual than the previous "no-wall chain", since wall *crossing* is
now proved.  We name it `GenericChainInput`, build the unconditional region
independence from it, and certify it non-vacuous. -/









/-! ### Non-vacuity of the residual

The residual is satisfiable: a `ρ` with `ρ.r = σ.r` (in particular the *reflexive*
pair) has the trivial chain `μ = ρ = σ`, since the constant segment avoids zero and
has no walls.  More substantively, two *same-side* directions admit the direct
length-1 chain `μ = σ`: the connecting segment stays nonzero (avoids the zero
direction) and is wall-free (generic).  So `GenericChainAt` is inhabited on genuinely
distinct directions, not just the diagonal — the discharge is not vacuous. -/









/-! ## Part 7: the unconditional Chapter-36 art-gallery headline (ray-choice free)

Feeding the discharged `UnconditionalRayIndepInput` into the downstream consumers:
the kept ray-choice oracle of `PolygonFinish` / `PolygonSeparation` is replaced by the
generic-chain residual, with wall crossing fully proved.  We state the clean headline:
given `GenericChainInput P` (plus the genuinely-planar split-set / base / merge
residuals the design already isolates), the art gallery bound holds for *any* ray
direction `ρ`, and the two-direction region statement is direction-independent. -/







end

end ProofsInTheBook.PolygonWallGlobal

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonWallGlobal
-/
/- Source module: ProofsInTheBook.PolygonGenericRay -/
section
set_option autoImplicit true


/-!
# Chapter 36 — generic-position existence for the wall-global ray independence
(`PolygonGenericRay`)

`PolygonWallGlobal` reduced the global ray-independence of Chapter 36 to a single
generic-position datum `GenericChainInput P`, bundling, for every pair of ray
directions and every off-boundary `x`, a connecting intermediate whose two segments
both `SegAvoidsZero` and `GenericWallSeg`.  This module **discharges that datum by the
finite bad-direction avoidance argument**, on the geometrically generic stratum, and
isolates with full honesty the single residual it does *not* absorb.

## The reduction: `GenericWallSeg` is a condition on `x` alone

The key structural fact (`genericWallSeg_of_offEdgeLines`) is that
`GenericWallSeg P r₁ r₂ x` depends on `r₁`, `r₂` only through `SegAvoidsZero`: a *wall*
parameter `t₀` has `dirAt r₁ r₂ t₀` parallel to `edgeVec i`; the wall is *generic*
(both endpoint side values nonzero) precisely when `x` is **not on the line of edge
`i`**, i.e. `det2 (edgeVec i) (P.q i − x) ≠ 0`.  Indeed if `ds0Of i t₀ = 0` too, then
the (nonzero, by `SegAvoidsZero`) direction is `det2`-orthogonal to *both* `edgeVec i`
and `P.q i − x`, forcing those two parallel — `x` on the edge line.  So whenever `x`
lies off *every* edge line, **every wall is generic, for every segment**.

## Finite avoidance on the direction circle

For an `x` off all edge lines, a connecting intermediate `μ` exists for *any* pair:
`GenericWallSeg` is then automatic on both segments, and `SegAvoidsZero` is a
finite-avoidance condition — the connecting segment `dirAt a b` hits the zero direction
only when `b` is a *negative* scalar multiple of `a` (antiparallel).  Choosing
`μ.r = mkPt 1 s` with `s` outside the finite bad set (edge slopes ∪ the at-most-two
antiparallel slopes of `ρ.r`, `σ.r`) yields a genuine `RayDirection` whose two
connecting segments avoid the zero direction.  This discharges `GenericChainAt P ρ σ x`
**unconditionally** for `x` off all edge lines.

## The isolated residual

When `x` *does* lie on the line of some edge `i`, and the two given directions `ρ`,
`σ` straddle that edge (opposite signs of `det2 · (edgeVec i)`), *every* connecting
path from `ρ` to `σ` must cross a wall of edge `i`, and at such a wall `x` is on the
ray line — a **degenerate** wall that `GenericWallSeg` (by construction) forbids.  The
single-intermediate `GenericChainAt` is genuinely obstructed there.  This residual —
`OnSomeEdgeLine`-coincidence of a vertex crossing with an edge-parallel direction — is
the measure-zero degenerate-sweep configuration the per-wall layer pairs only on the
generic stratum.  It is isolated as the one honest residue `GenericChainInput`, with
the unconditional discharge proved on the `OffAllEdgeLines` stratum.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PolygonGenericRay

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonRayIndep
open ProofsInTheBook.PolygonIccEngine
open ProofsInTheBook.PolygonFinish
open ProofsInTheBook.PolygonWall
open ProofsInTheBook.PolygonWallGlobal
open ProofsInTheBook.PolygonLocalConstancy
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the reduction — `GenericWallSeg` from `x` off all edge lines

`x` lies *off the line of edge `i`* when `det2 (edgeVec i) (P.q i − x) ≠ 0` (the three
points `x`, `P.q i`, `P.q (cyclicNext i)` are not collinear).  `OffAllEdgeLines P x`
asks this for every edge.  We show it forces every wall along any nonzero-direction
segment to be generic. -/









/-! ## Part 2: `SegAvoidsZero` to a `mkPt 1 s` direction by finite avoidance

The connecting segment `dirAt a b` passes through the zero direction only when `b` is
a negative multiple of `a`.  For `b = mkPt 1 s = (1, s)` this pins `s = a₁ / a₀` and
requires `a₀ < 0`; avoiding that single slope keeps the segment nonzero. -/





/-! ## Part 3: a generic connecting intermediate on the off-edge-lines stratum

For `x` off every edge line we build the connecting intermediate `μ.r = mkPt 1 s`
avoiding the finitely many bad slopes: the edge slopes (so `μ` is a genuine
`RayDirection`) and the antiparallel slopes of `ρ.r`, `σ.r` (so both segments avoid the
zero direction).  `GenericWallSeg` is then automatic for both segments. -/



/-! ## Part 4: the genuine obstruction on the on-edge-line stratum

`genericChainAt_of_offAllEdgeLines` discharges the generic-chain datum **for every**
off-boundary `x` lying off all edge lines, with *no* extra hypothesis — finite
bad-direction avoidance is complete there.  The remaining stratum, `x` *on the line* of
some edge, is **not** an avoidance gap: it is a genuine obstruction to the
`GenericChainAt` *interface* itself.

The mechanism, proved precisely below.  At a wall `t₀` of edge `i` (`dir ∥ edgeVec i`),
if `x` is *on* edge `i`'s line then both endpoint side values vanish
(`genericWallSeg_fails_on_edge_line`): the wall is **degenerate**, and `GenericWallSeg`
— which demands both side values *nonzero* at every wall — is violated.  A connecting
*straight segment* between two directions on strictly opposite sides of edge `i`
(`det2 · (edgeVec i)` of opposite sign) is forced through such a wall
(`segment_has_wall_of_straddle`): the affine wall function changes sign on `[0,1]`,
hence vanishes there.  So for two directions straddling an `x`-collinear edge, **no**
single-intermediate `GenericChainAt P ρ σ x` can hold — both sub-segments would have to
keep `det2 · (edgeVec i)` of one fixed sign, impossible across a straddle.

Consequently `GenericChainInput P` (∀ pair, ∀ off-boundary `x`) is **false** for any
polygon admitting an off-boundary `x` on some edge line together with a straddling pair
— which is generic.  The route to the *unconditional* `UnconditionalRayIndepInput` /
`artGallery_strict` therefore cannot factor through `PolygonWallGlobal`'s
`GenericChainInput`; it requires the **degenerate-wall parity transport** (the per-edge
`rfcount_eventually_zero_of_degenerateWall` of `PolygonWall` *globally assembled
without* `GenericWallSeg`), which `PolygonWallGlobal` left gated behind `GenericWallSeg`
and is the genuine analytic residue.  We record the obstruction rigorously here. -/







end

end ProofsInTheBook.PolygonGenericRay

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonGenericRay
-/
/- Source module: ProofsInTheBook.PolygonDegenerateWall -/
section
set_option autoImplicit true


/-!
# Chapter 36 — degenerate-wall parity transport for TRIANGLES (`PolygonDegenerateWall`)

`PolygonWallGlobal` assembled the per-wall local-zero layer of `PolygonWall` into the
global parity-constancy `rcrossSum_parity_eventually_const`, but **gated behind the
generic-wall residual `GenericWallSeg`**: at a *wall* `t₀` (`dirDen i t₀ = 0`) the
assembly demanded both endpoint side values nonzero, which fails exactly on the
**degenerate wall** (`x` on edge `i`'s line, `ds0Of i t₀ = 0`).  `PolygonGenericRay`
showed this residual is *false in general* and discharged only the off-edge-line
stratum.

This module removes the gate **for triangles** (`n = 3`), unconditionally.  The
mechanism (numerically confirmed in the prior round): at a degenerate wall of edge `w`,
the wall edge contributes `0` (`PolygonWall.rfcount_eventually_zero_of_wall`, which is
already unconditional), and the **two non-wall edges flip together** — their combined
crossing count has *even* parity in a whole neighbourhood, so the total parity is
locally constant.  The two non-wall edges are `cyclicNext w` and `cyclicPrev w`; they
share the unique off-line vertex `P.q (cyclicNext (cyclicNext w))`, while their other
two vertices are the two endpoints of the wall edge `w`, which lie on the ray line and
whose side functions are **positively proportional** (`x` outside the segment, off the
boundary) — so the span of those two endpoints is always false and the pair count is
even.  The `span_mod_two_through_vertex` truth table absorbs the shared off-line vertex.

Since a non-degenerate triangle has three pairwise-non-parallel edge directions, at any
probe parameter the direction is parallel to **at most one** edge, so there is at most
one wall; case-splitting on whether that wall is degenerate (`x` on its line) gives a
clean, hypothesis-free per-`t₀` parity-constancy lemma.  Chaining through one
antiparallel-avoiding intermediate then discharges the full
`UnconditionalRayIndepInput Q` for every triangle, **unconditionally** — feeding
`PolygonSeparation.triangleExteriorEven_of_rayIndep` and the fully unconditional
`artGallery_strict`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PolygonDegenerateWall

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonVertexSweep
open ProofsInTheBook.PolygonRayIndep
open ProofsInTheBook.PolygonIccEngine
open ProofsInTheBook.PolygonFinish
open ProofsInTheBook.PolygonWall
open ProofsInTheBook.PolygonWallGlobal
open ProofsInTheBook.PolygonGenericRay
open ProofsInTheBook.PolygonLocalConstancy
open Filter Topology
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the local generic-wall hypothesis and the generic per-`t₀` assembly

`rcrossSum_parity_eventually_const` of `PolygonWallGlobal` uses its global
`GenericWallSeg` hypothesis **only at the single parameter `t₀`**.  We re-derive that
per-`t₀` statement under the strictly local hypothesis `LocalGenericWall … t₀` (every
wall at `t₀` is generic), so it can be discharged at a parameter even when the segment
has degenerate walls *elsewhere*.  The proof is the assembly of `PolygonWallGlobal`
with the global `hgen t₀ ht₀` call replaced by the local hypothesis. -/





/-! ## Part 2: cyclic combinatorics for the triangle (`n = 3`)

A non-degenerate triangle has three edges forming a `3`-cycle.  We record the two
cyclic identities the degenerate-wall pairing needs:
`cyclicNext (cyclicNext w) = cyclicPrev w` and (its consequence)
`cyclicNext (cyclicNext (cyclicNext w)) = w`. -/





/-! ## Part 3: the degenerate-wall double-event pairing (the new math)

At a *degenerate* wall of edge `w` (`dirDen w t₀ = 0` and `ds0Of w t₀ = 0`, i.e. `x` on
edge `w`'s line) off the boundary, the wall edge contributes `0` near `t₀`
(`rfcount_eventually_zero_of_wall`), and the two adjacent edges `j = cyclicNext w` and
`p = cyclicNext j` carry **equal** crossing counts near `t₀`, hence an even pair sum.

The two key geometric facts, both flowing from the positive proportionality
`P.q w − x = μ • (P.q (cyclicNext w) − x)` (`μ > 0`, `x` outside the wall segment):

* **Span agreement** — `ds0Of j = ds1Of w = side (P.q (cyclicNext w))` and
  `ds1Of p = ds0Of w = side (P.q w)` are positively proportional, while the shared
  vertex `ds1Of j = ds0Of p = side (P.q (cyclicNext (cyclicNext w)))` is common; `Span`
  is symmetric and sign-only, so `Span (ds0Of j) (ds1Of j) ↔ Span (ds0Of p) (ds1Of p)`
  pointwise.
* **Forward agreement** — at `t₀` the ray reaches `P.q (cyclicNext w)` (edge `j`'s start)
  and `P.q w` (edge `p`'s end) at forward parameters in positive proportion
  `dirTau p t₀ = μ • dirTau j t₀`, both nonzero (off boundary), so the forward guards
  `0 ≤ dirTau j` and `0 ≤ dirTau p` agree in a neighbourhood. -/









/-! ## Part 4: hypothesis-free per-`t₀` parity constancy for the triangle

For `n = 3`, at any probe parameter `t₀` with `dirAt r₁ r₂ t₀ ≠ 0`, the direction is
parallel to **at most one** edge (the three edge directions are pairwise non-parallel),
so there is at most one wall.  Case-splitting on whether a *degenerate* wall (`x` on its
line) exists at `t₀`:

* **No degenerate wall** — `LocalGenericWall` holds, so `rcrossSum_parity_eventually_const_local`
  gives parity constancy.
* **A degenerate wall** of edge `w` — the wall edge contributes `0` and the two adjacent
  edges carry equal counts (`rfcount_pair_eventually_eq_of_degenerateWall_tri`), so
  `rcrossSum % 2 = 0` in a whole neighbourhood, hence constant. -/







/-! ## Part 5: global parity constancy on `[0,1]` and the wall-global ray independence

The `Icc 0 1` engine of `PolygonWallGlobal` (preconnectedness + local constancy), now
fed by the *hypothesis-free* per-`t₀` lemma, gives equal endpoint parities for any
segment that avoids the zero direction — **no `GenericWallSeg`**. -/









/-! ## Part 6: the avoid-zero chain and the unconditional triangle ray-independence

Two arbitrary ray directions are connected through a single intermediate `μ = mkPt 1 s`
whose slope avoids the (finite) edge slopes (so `μ` is a genuine `RayDirection`) and the
at-most-two antiparallel slopes of `ρ.r`, `σ.r` (so both connecting segments avoid the
zero direction).  No genericity at the walls is required — `closedRegion'_wallGlobal_tri`
handles every wall.  Composing the two region transports discharges the full
`UnconditionalRayIndepInput Q`, **unconditionally**. -/





/-! ## Part 7: the fully unconditional Chapter-36 art-gallery headline

Feeding `unconditionalRayIndepInput_triangle` into
`PolygonSeparation.triangleExteriorEven_of_rayIndep` discharges the triangle leaf's
exterior-even atom **with no ray/genericity hypothesis**, hence the
`PolygonSeparation.chapter36_headline_separation` art-gallery bound is unconditional in
the ray choice (the remaining inputs being the genuinely-planar residuals the design
already isolates: the uniform residual geometry `D`, the convex-vertex leaf primitive
`hconv`, and the diagonal-attach peel `M`). -/



/-- **Chapter-36 art-gallery headline, unconditional in the ray choice.**  The kept
ray-choice oracle of `PolygonSeparation.chapter36_headline_separation`
(`∀ Q : StrictSimplePolygon 3, UnconditionalRayIndepInput Q`) is now *produced*
unconditionally by `unconditionalRayIndepInput_triangle`, so the `⌊n/3⌋` guard bound
holds for *any* ray direction `ρ` with no ray/genericity hypothesis. -/
theorem artGallery_strict_unconditional {n : ℕ}
    (D : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
        ProofsInTheBook.PolygonOracleClose.ResidualGeometryData P ρ)
    (hconv : ProofsInTheBook.PolygonLeaf.TriangleConvexLeaf)
    (M : ProofsInTheBook.PolygonLast.DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms hconv
          triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, ProofsInTheBook.PolygonRayIndep.Sees P ρ (P.q v) x :=
  ProofsInTheBook.PolygonSeparation.chapter36_headline_separation D hconv
    unconditionalRayIndepInput_triangle M P ρ

end

end ProofsInTheBook.PolygonDegenerateWall

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonDegenerateWall
-/
/- Source module: ProofsInTheBook.PolygonGeometryData -/
section
set_option autoImplicit true


/-!
# Chapter 36 — the last planar residuals, isolated honestly (`PolygonGeometryData`)

This module sits at the very top of the Chapter-36 strict-polygon stack and
examines the three residual hypotheses still standing in
`PolygonDegenerateWall.artGallery_strict_unconditional`:

1. `hconv : TriangleConvexLeaf` — for every strict simple `3`-gon and ray
   direction `σ`, the closed hull of the three vertices is contained in the
   ray-crossing region (`IsConvexVertex' Q σ ⟨1⟩`, i.e.
   `closedTri (q0) (q1) (q2) ⊆ {x | ClosedRegion' Q σ x}`).
2. `D : ∀ {m} (P) (ρ), ResidualGeometryData P ρ` — the per-polygon
   diagonal-cut planar data (convex extreme vertex, transversality dispatcher,
   sub-polygon strictness axioms, common sub-rays, half-plane disjointness, the
   boundary union datum, and the intersection-equals-diagonal datum).
3. `M : DiagonalAttachInput …` — the universal diagonal-attachment peel-reordering
   certificate.

## What this module establishes

The ray-crossing **parity/count** core of Chapter 36 is fully discharged below
us (`unconditionalRayIndepInput_triangle`, `triangleExteriorEven_unconditional`,
both unconditional).  What the three residuals above package is the chapter's
genuinely **planar / finite-Jordan** content — region containment of a convex
vertex's adjacent triangle, half-plane disjointness of the two sub-regions of a
diagonal cut, the shared-boundary identity, and the combinatorial peel order.
The substrate of Chapters 36's stack is built **without a Jordan curve theorem**:
it supplies a *finite-Jordan substitute* (boundary-free local constancy of the
region indicator, `openSegment_region'_const_of_boundary_free`, already
unconditional) but **no** machinery that produces an interior region *seed* or a
convex-position separation from first principles.  The three residuals are
exactly the points where such Jordan/convex-position content is required, and the
design isolates them as inputs rather than re-deriving them.

Concretely (see the field-by-field analysis in Part 5 below):

* `IsConvexVertex' P ρ i` is *definitionally* "the adjacent triangle of `i` lies
  inside the closed region" (`PolygonSideCrossing.IsConvexVertex'`); it is the
  same Jordan datum the development never proves from the substrate (its general
  form `exists_convex_vertex` is *stated relative to* the residue bundle
  `ExtremeConvexResidue`, which carries the convexity as a hypothesis).
* `OffDiagDisjoint` is declared, at its definition site
  (`PolygonOracle.OffDiagDisjoint`), to be *"the irreducibly-geometric half-plane
  separation"*.
* `DiagonalAttachInput` is declared, at its definition site
  (`PolygonLast`), to be *"a strong hypothesis"* whose only obligation we discharge
  here is **non-vacuity**.

Accordingly this module's contribution is the playbook §3.3 **anti-vacuity /
faithfulness** layer for the three residuals, together with the assembled
conditional headline:

* `triangleConvexLeaf_nonvacuous` — the convex-vertex leaf datum is *satisfiable*
  (a concrete `3`-gon with a ray for which `IsConvexVertex' … ⟨1⟩` holds is
  exhibited via the genuine region-containment of a boundary point), so `hconv`
  is not a disguised `False`.
* `residualGeometryData_nonvacuous` — `ResidualGeometryData` is inhabited
  *exactly when* a genuine `CutGeometry` with common rays and half-plane
  disjointness is (`residualGeometryData_of_cutGeometry`); so `D` is a faithful
  decomposition, not a strengthening.
* `diagonalAttachInput_attach_nonvacuous` — the `AttachesTo` predicate underlying
  `DiagonalAttachInput` is inhabited (`attachesTo_nonvacuous`), so `M` is not a
  trivially-unsatisfiable premise.
* `artGallery_strict` — the assembled `⌊n/3⌋` art-gallery headline, conditional on
  exactly the three residuals, threading the unconditional parity core.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonGeometryData

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonTriangulation
open ProofsInTheBook.PolygonLeaf
open ProofsInTheBook.PolygonOracleClose
open ProofsInTheBook.PolygonRayIndep (Sees)
open ProofsInTheBook.Chapter36
open ProofsInTheBook.PolygonCutOracle (CutGeometry)
open ProofsInTheBook.PolygonOracle (CommonRay OffDiagDisjoint)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput AttachesTo )

noncomputable section

variable {n : ℕ}

/-! ## Part 1: faithfulness of the convex-vertex leaf residual `hconv`

`TriangleConvexLeaf` asks that for every `3`-gon `Q` and ray `σ`, the adjacent
triangle of the middle vertex `⟨1⟩` (which, for a `3`-gon, *is* the whole closed
hull `closedTri (q0) (q1) (q2)`) lies inside the closed region.  This is the
development's single irreducible planar primitive `IsConvexVertex'`.

We certify it is **satisfiable** (not a disguised `False`): every *boundary* point
of a triangle is in the closed region, and the three vertices are boundary points,
so `IsConvexVertex'` restricted to the hull's vertices already holds — and more
sharply, the predicate as a whole is the genuine "hull ⊆ region" containment that
holds for a real triangle (the substrate's `region_subset`/`hull_subset` split is
exactly this, with the *hard* half being precisely this primitive). -/





/-! ## Part 2: faithfulness of the residual geometry data `D`

`ResidualGeometryData P ρ` bundles the irreducible planar fields of one diagonal
cut.  Its non-vacuity certificate already lives in `PolygonOracleClose`
(`residualGeometryData_of_cutGeometry`): a *genuine* `CutGeometry` whose sub-rays
are common (`CommonRay`) and whose sub-regions are half-plane disjoint
(`OffDiagDisjoint`) produces a `ResidualGeometryData`.  We re-export it here as the
faithfulness certificate for `D`. -/





/-! ## Part 3: faithfulness of the diagonal-attach residual `M`

`DiagonalAttachInput B` is the universal peel-reordering certificate.  Its
underlying combinatorial predicate `AttachesTo` is inhabited
(`PolygonLast.attachesTo_nonvacuous`): a single triangle attaches to a singleton
triangulation along a shared edge with a fresh apex — the shape of every diagonal
merge leaf.  We re-export this as the non-vacuity certificate for `M`. -/



/-! ## Part 4: the assembled conditional Chapter-36 art-gallery headline

Threading the three residuals through the unconditional parity core
(`PolygonDegenerateWall.artGallery_strict_unconditional`, whose ray-choice oracle
`unconditionalRayIndepInput_triangle` is already discharged).  The statement's
*only* hypotheses are the three named planar/combinatorial residuals; everything
count/parity is closed below. -/



/-! ## Part 5: precise residue analysis — why these three are irreducible *here*

The honest status of each residual, with the concrete blocking content named.

### `hconv : TriangleConvexLeaf` — blocked on the *interior odd-crossing seed*

`IsConvexVertex' Q σ ⟨1⟩` unfolds to `closedTri (q0)(q1)(q2) ⊆ ClosedRegion'`.
For an *off-boundary* point `x` of the hull this is `Odd (CrossingNumber' Q σ x)`.
The substrate supplies (all unconditional):

* `closedRegion'_of_onBoundary` — boundary points are in the region (so the three
  vertices and the three edges are covered, `hull_vertices_mem_region`);
* `openSegment_region'_const_of_boundary_free` — region constancy along a
  boundary-free open segment (the finite-Jordan substitute, *no* Jordan curve
  theorem); and
* `exists_crossingNumber'_eq_zero` — a far *exterior* point with crossing `0`
  (an *even* seed) plus ray-independence.

What is **missing** is a single *interior* region seed: a point of the open hull
with provably *odd* crossing number.  The natural witness is the centroid `g`,
for which the three side coordinates satisfy `side σ.r g q0 + side σ.r g q1 +
side σ.r g q2 = 0` (linearity of `det2` on `(q0-g)+(q1-g)+(q2-g) = 0`); hence for
a vertex-line-avoiding ray exactly *two* edges `Span` (the two incident to the
lone-sign vertex).  The residual obstruction is then the *forward-guard* count:
showing **exactly one** of those two spanning edges has `0 ≤ crossTau` (the ray
meets the boundary once forward, once backward), which is precisely the
single-edge-jump / half-plane Jordan content the chapter keeps as a named input
(`PolygonSeparation`'s file header, lines 42–49: *"the irreducible
single-edge-jump / half-plane Jordan content that the entire Chapter-36 stack
keeps as a named input"*).  No lemma in the substrate computes the *sign* of
`crossTau` from the geometry, so the centroid-odd seed cannot be produced.

### `D` — blocked on `convexVertex_spec` and `OffDiagDisjoint`

`ResidualGeometryData.convexVertex_spec : IsConvexVertex' P ρ convexVertex` is the
same "adjacent triangle ⊆ closed region" containment, now for a *general* polygon.
Its general-polygon form `PolygonConvexVertex.exists_convex_vertex` is **stated
relative to** the residue bundle `ExtremeConvexResidue`, which *carries the
convexity as a hypothesis* — nothing in the substrate derives it.  The `disjoint`
field is `OffDiagDisjoint`, declared at its definition
(`PolygonOracle.OffDiagDisjoint`) to be *"the irreducibly-geometric half-plane
separation"*.  Both require convex-position / half-plane Jordan content absent
from the substrate.  Faithfulness is certified by
`residualGeometryData_nonvacuous` (a genuine `CutGeometry` produces a
`ResidualGeometryData`), so `D` is a faithful decomposition, not a strengthening.

### `M` — blocked on the *peel-reordering* witness

`DiagonalAttachInput` is declared (`PolygonLast`, lines 472–475) *"a strong
hypothesis (universal …)"*; the file discharges only its *index-freshness*
content (via the proved `leftRight_image_inter`) and certifies *non-vacuity*
(`attachesTo_nonvacuous`, re-exported as
`diagonalAttachInput_attach_nonvacuous`).  The remaining peel-reordering of an
arbitrary binary-tree triangulation into a diagonal-first linear peel is the
isolated combinatorial residual.

**Conclusion.**  The three residuals are exactly the Jordan / convex-position /
peel-order content that the Chapter-36 substrate is *architected to isolate*
(it provides a finite-Jordan *substitute* — boundary-free local constancy — but
no Jordan curve theorem, no convex-position separation, no interior region seed).
They cannot be discharged from the substrate without building such a layer; this
module certifies their *faithfulness* (non-vacuity) and assembles the conditional
headline `artGallery_strict`, with the entire parity/count core unconditional
below. -/

end

end ProofsInTheBook.PolygonGeometryData

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonGeometryData
-/
/- Source module: ProofsInTheBook.PolygonTriangleConvex -/
section
set_option autoImplicit true


/-!
# Chapter 36 — the convex-vertex triangle leaf, UNCONDITIONAL (`TriangleConvexLeaf`)

This file discharges the `hconv` oracle of `artGallery_strict_unconditional`: the
convex-vertex half of the triangle leaf,

```
TriangleConvexLeaf := ∀ (Q : StrictSimplePolygon 3) (σ : RayDirection Q),
  IsConvexVertex' Q σ ⟨1⟩
```

which (by `base_subset_iff_convexVertex_one`) is exactly the containment
`closedTri (v0 Q) (v1 Q) (v2 Q) ⊆ {x | ClosedRegion' Q σ x}`.

## The crossTau-sign lemma (the geometric heart)

Fix a triangle `Q` with vertices `q0, q1, q2` and oriented area
`O := orient q0 q1 q2 ≠ 0`.  For a base point `x = w0•q0 + w1•q1 + w2•q2` with
barycentric weights `w0, w1, w2 ≥ 0` summing to `1`, and a *valid* ray direction
`r` (not edge-parallel), the three side coordinates `s_k := side r x (q_k)` satisfy
the **barycentric side identity**

```
w0•s0 + w1•s1 + w2•s2 = side r x x = det2 r 0 = 0.
```

The crossTau numerator has the closed form (purely from `det2` bilinearity)

```
crossTau_i • crossDen_i = det2 (q_i - x) (q_{i+1} - q_i) = w_{i+2} • O
```

where `w_{i+2}` is the weight of the vertex *opposite* edge `i`.  Hence for a
*strictly interior* point (all `w_k > 0`) and a ray avoiding every vertex
(`s_k ≠ 0`):

* the weighted-zero identity forces the three `s_k` to NOT all share one strict
  sign — exactly one of them, `s_m`, carries the lone sign;
* the two edges incident to `q_m` are exactly the two that `Span` (opposite end
  signs); the third edge joins two same-sign vertices, so it does not span;
* those two spanning edges have `crossDen`s of *opposite* sign (`s_m - s_{m-1}`
  versus `s_{m+1} - s_m`, with `s_m` the lone sign), so since
  `crossTau_i = w_{i+2}•O / crossDen_i` with `w_{i+2} > 0`, their `crossTau`s have
  opposite sign — **exactly one is `≥ 0`** (forward).

Therefore the forward crossing count is `1`, i.e. `CrossingNumber' Q r x` is odd.
Ray-independence of the off-boundary parity (`crossingNumber'_wallGlobal_tri`,
already unconditional) transports this to the polygon's own ray `σ`.

A point of the closed triangle with some weight `= 0` lies on a triangle edge,
hence `OnBoundary` — the `Or.inl` branch of `ClosedRegion'`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonTriangleConvex

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonTriangulation (v0 v1 v2)
open ProofsInTheBook.PolygonLeaf

noncomputable section

/-! ## Part 1: barycentric extraction from a triangle hull membership

A point of `closedTri a b c = convexHull ℝ {a,b,c}` is a barycentric combination
of the three vertices.  We extract explicit nonnegative weights summing to one via
`convexJoin_singleton_segment`. -/



/-! ## Part 2: the barycentric side identity and the crossTau closed form

For `x = w0•q0 + w1•q1 + w2•q2` with `w0+w1+w2 = 1`, the side coordinates obey
`∑ w_k • side r x q_k = 0` (linearity of `det2` and `side r x x = 0`).  The
crossTau numerator of edge `i` is `w_opp • orient`, with `w_opp` the weight of the
vertex opposite edge `i`. -/







/-! ## Part 3: the Fin-3 setup — three vertices, three weights, three side values

We now fix a triangle `Q` and work with `q0 = Q.q ⟨0⟩`, `q1 = Q.q ⟨1⟩`,
`q2 = Q.q ⟨2⟩` and the cyclic edges.  The crossTau numerators of the three edges
factor as `w_opp • orient`. -/









/-! ## Part 4: the pure-arithmetic forward count for a triangle interior

Three nonzero side values that are *not* all of one strict sign (forced by the
barycentric identity with positive weights), and a nonzero orient: the three
cyclic edge indicators (Span + forward-product-sign) sum to exactly `1`. -/







/-! ## Part 5: the polygon-level interior-odd crossing number

We instantiate `forward_count_eq_one` against the actual triangle.  The forward
guard `0 ≤ crossTau` is rewritten (via `crossTau_nonneg_iff`,
`crossTau_mul_crossDen`, `crossNum_eq_weight_orient`, `side_next_sub_side`) into
the arithmetic forward-product condition. -/



/-! ## Part 6: a valid ray missing every vertex of the ray line through `x`

For a point `x` distinct from all three vertices, there is a valid `RayDirection`
(`mkPt 1 t`) whose ray line through `x` passes through *no* vertex
(`side r x q_k ≠ 0` for all `k`) — avoid the finitely many bad slopes (edge-
parallel and the three vertex-alignment slopes). -/





/-! ## Part 7: a strictly-interior point is off the boundary

For `x = w0•q0 + w1•q1 + w2•q2` with all weights `> 0`, `orient q0 q1 x` equals
`w2 • orient q0 q1 q2 ≠ 0`, so `x` is not collinear with edge `q0 q1`; cyclically,
`x` lies on no edge of the triangle, hence off the polygon boundary. -/







/-! ## Part 8: assembly — `TriangleConvexLeaf` unconditional

Every point of `closedTri q0 q1 q2` is in `ClosedRegion' Q σ`: a barycentric point
with some zero weight is on an edge (boundary, `Or.inl`); a strictly-interior point
is off the boundary with `CrossingNumber' Q r x = 1` (odd) for a vertex-avoiding
valid ray `r`, transported to `σ` by the unconditional ray-independence
`closedRegion'_chain_tri`. -/







/-! ## Part 9: the Chapter-36 headline over only TWO remaining oracles

With `hconv` (`TriangleConvexLeaf`) now discharged unconditionally and
`TriangleExteriorEven` already unconditional
(`PolygonDegenerateWall.triangleExteriorEven_unconditional`), the art-gallery
`⌊n/3⌋` headline is conditional on only the two genuinely-irreducible planar
inputs: the uniform residual geometry `D` and the diagonal-attach peel `M`. -/

/-- **Chapter-36 art-gallery headline over two oracles (`D`, `M`).**  Every strict
simple polygon with a ray direction admits `≤ ⌊n/3⌋` vertex guards seeing its whole
closed region, conditional on exactly the residual geometry data `D` and the
diagonal-attach peel `M` — the convex-vertex leaf (`hconv`) is now supplied
unconditionally by `triangleConvexLeaf_holds` (and `TriangleExteriorEven` by the
degenerate-wall transport).  Three oracles reduced to two. -/
theorem artGallery_strict {n : ℕ}
    (D : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
        ProofsInTheBook.PolygonOracleClose.ResidualGeometryData P ρ)
    (M : ProofsInTheBook.PolygonLast.DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, ProofsInTheBook.PolygonRayIndep.Sees P ρ (P.q v) x :=
  ProofsInTheBook.PolygonDegenerateWall.artGallery_strict_unconditional
    D triangleConvexLeaf_holds M P ρ

end

end ProofsInTheBook.PolygonTriangleConvex

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonTriangleConvex
-/
/- Source module: ProofsInTheBook.PolygonResidualData -/
section
set_option autoImplicit true


/-!
# Chapter 36 — the `ResidualGeometryData` supplier (the `D` oracle), isolated

This file attacks the `D` oracle of the Chapter-36 art-gallery headline: the
*uniform supplier*

```
residualGeometryData_of_polygon :
  ∀ {m} (P : StrictSimplePolygon m) (ρ : RayDirection P), ResidualGeometryData P ρ
```

that `cutGeometryOracle_of_data` and `artGallery_strict` consume.

## Honest verdict (genuine, source-level exhaustion)

A *fully unconditional* `residualGeometryData_of_polygon` is **NOT** constructible
from the Chapter-36 substrate.  Every substantive field of `ResidualGeometryData`
is a per-polygon planar Jordan / convex-position / half-plane primitive that the
substrate is *architected to isolate*, with **no producer** from a bare
`StrictSimplePolygon` + `RayDirection`:

* `convexVertex_spec : IsConvexVertex' P ρ i` — for a *general* `n`-gon this is the
  containment `closedTri (q prev) (q i) (q next) ⊆ region`.  The substrate's only
  route, `PolygonConvexVertex.exists_convex_vertex`, is **stated relative to**
  `ExtremeConvexResidue`, a bundle that *carries the convexity as a hypothesis*
  (`PolygonConvexVertex.lean:215-243`: "the one genuinely region-level fact whose
  proof needs the parity machinery applied to the extreme/lexicographic vertex; the
  substrate exposes it as a residue").  The unconditional triangle template
  `PolygonTriangleConvex.triangleConvexLeaf_holds` works only at `n = 3`, where the
  adjacent triangle equals the whole hull, so its three edges *are* the polygon's
  three edges and `crossingNumber'_interior_eq_one` (a sum over **all** polygon
  edges) applies.  For general `n` the adjacent triangle's third side is a *chord*,
  not a polygon edge, and the interior-odd argument does not transfer.

* `transversality : DiagonalTransversality' P ρ i` — packs `EarTransversality'` /
  `SlideTransversality'`, i.e. boundary-freeness of the open ear/slide segments
  (`PolygonSideCrossing.lean:1204-1283`).  This is genuine Jordan content (a segment
  avoiding the boundary); `exists_diagonal'` itself *consumes* it, never produces it.

* `leftAxioms` / `rightAxioms : LeftStrictAxioms / RightStrictAxioms` — these carry
  `noncollinear` (the diagonal-endpoint triples *could* be collinear) and
  `edge_inter` (the diagonal edge meets the arc edges properly).  The source flags
  exactly these as "the genuine planar content at a cut … the two
  `StrictSimplePolygon` axioms that are *not* combinatorial"
  (`PolygonCutOracle.lean:250-255`).  No producer.

* `leftRay` / `rightRay` / `commonRay` — `CommonRay` *is* satisfiable
  (`PolygonOracleClose.commonRayDir_valid_for₃`: a single slope outside the union of
  the parent's and both sub-polygons' edge slopes gives one `mkPt 1 t*` valid for
  all three).  But the `commonRay` field demands `(leftRay h).r = ρ.r` for the
  **prescribed** parent `ρ` — and `ρ.r` may be parallel to a sub-polygon edge, so a
  *given* `ρ` need not be a valid direction for the sub-polygons.  Hence the rays
  cannot be derived freely for an arbitrary `ρ`; they are part of the irreducible
  per-cut datum.

* `disjoint : OffDiagDisjoint` — declared, at its definition site
  (`PolygonOracle.OffDiagDisjoint`, lines 547-557), to be *"the irreducibly-geometric
  half-plane separation"*: off all three boundaries no point lies in *both*
  sub-regions.  Because `ClosedRegion'` is defined by the **parity** of the
  crossing number (`OnBoundary ∨ Odd (CrossingNumber')`), not by a `det2` half-plane
  sign, there is no separating-line shortcut: the link between crossing-parity and
  the half-plane geometry *is* the Jordan content the substrate lacks.

* `boundary` / `intersection` — the boundary-points union datum and the
  intersection-equals-diagonal datum: the remaining Jordan-region split content.

So the `D` oracle is, by construction, the bundle of irreducible planar inputs;
discharging it unconditionally is a *separate* Jordan-curve / convex-position
campaign (hundreds of lines), not a residue closable from the substrate.  This
matches two prior independent analyses (`opus-geomdata-reply.md`,
`opus-triconvex-reply.md`).

## What this file *does* deliver (faithful, non-vacuous, NOT a re-wrapper)

Per the playbook §3.3 discipline (never fake a vacuous/over-strong discharge), we
isolate the irreducible content as a **single named honest input** strictly smaller
than `D`, and prove the genuine reductions around it:

1. **`PolygonCutInput`** — the *one* isolated uniform planar input: for every
   polygon and ray, a genuine `CutGeometry` together with the *common-ray* condition
   (`CommonRay`, satisfiable) and the *half-plane disjointness* (`OffDiagDisjoint`,
   the irreducible separation).  This is **strictly smaller** than a uniform
   `ResidualGeometryData`: the union field's count/parity half is *derived*, not
   carried (see point 2).

2. **`residualGeometryData_of_polygon`** — the `D` supplier, **conditional on
   `PolygonCutInput`**.  It is *not* a co-extensive re-wrapper of
   `ResidualGeometryData`: it builds each `ResidualGeometryData` via
   `residualGeometryData_of_cutGeometry`, whose `boundary` field is *derived* from
   the real `split_region_union` set equality (the count/parity half), with only
   `disjoint` / `intersection` carried verbatim.  The `commonRay` field is met by
   the `CutGeometry`'s own rays under the supplied `CommonRay`.

3. **`artGallery_strict_one_input`** — the Chapter-36 `⌊n/3⌋` headline, conditional
   on exactly the **single** isolated planar input `PolygonCutInput` and the peel
   oracle `M`.  This collapses the seven planar fields of the `D` oracle into one
   named bundle (with the union/parity half discharged), so the geometric surface is
   now `PolygonCutInput` + `M`.

4. **`polygonCutInput_nonvacuous`** — the §3.3 anti-vacuity certificate:
   `PolygonCutInput` is inhabited *exactly when* a uniform `CutGeometry` with common
   rays and half-plane disjointness is; it is not an unsatisfiable premise.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonResidualData

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonOracle (CommonRay OffDiagDisjoint)
open ProofsInTheBook.PolygonOracleClose
  (ResidualGeometryData residualGeometryData_of_cutGeometry cutGeometryOracle_of_data
   baseTriangleFacts_of_leaf)
open ProofsInTheBook.PolygonRayIndep (Sees)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)

/-! ## Part 1: the single isolated uniform planar input

`PolygonCutInput` bundles, uniformly over all polygons and rays, the irreducible
Jordan data: a `CutGeometry` (convex vertex, transversality, the cut strict-axioms,
the common-direction sub-rays, the region union / intersection identities) together
with the two residual conditions the count/parity reduction needs — the common-ray
condition `CommonRay` (satisfiable) and the half-plane disjointness `OffDiagDisjoint`
(the irreducible separation).  It is *strictly smaller* than a uniform
`ResidualGeometryData`: it does not carry a separate boundary union datum (that is
*derived* from `split_region_union` below). -/



/-! ## Part 2: the `D` supplier from the single input (union/parity half derived)

`residualGeometryData_of_cutGeometry` turns one `(CutGeometry, CommonRay,
OffDiagDisjoint)` into one `ResidualGeometryData`, deriving the boundary field from
the genuine `split_region_union` set equality (the count/parity half) and carrying
`disjoint` / `intersection` verbatim.  Applying it uniformly gives the supplier the
`D` oracle demands — conditional on the single isolated `PolygonCutInput`. -/





/-! ## Part 3: the Chapter-36 headline over a single planar input + `M`

Feeding the derived `D` supplier into `PolygonTriangleConvex.artGallery_strict`
(whose `hconv` triangle leaf is already unconditional) gives the `⌊n/3⌋` art-gallery
conclusion, conditional on exactly the single isolated planar input
`PolygonCutInput` and the peel oracle `M`. -/

/-- **Chapter-36 art-gallery `⌊n/3⌋` headline over one isolated planar input.**
Given the single uniform planar input `H : PolygonCutInput` (the irreducible
convex-vertex / transversality / cut-axioms / common-ray / half-plane-disjointness
data) and the diagonal-attach peel oracle `M`, every strict simple polygon with a
ray admits `≤ ⌊n/3⌋` vertex guards seeing its whole closed region.  The seven planar
fields of the `D` oracle are collapsed into the single bundle `H` (with the union
field's count/parity half discharged); the convex-vertex triangle leaf is supplied
unconditionally by `triangleConvexLeaf_holds`. -/
theorem artGallery_strict_one_input {n : ℕ}
    (H : PolygonCutInput)
    (M : DiagonalAttachInput
      (baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
          ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  ProofsInTheBook.PolygonTriangleConvex.artGallery_strict
    (residualSupply_of_input H) M P ρ

/-! ## Part 4: non-vacuity / faithfulness of the isolated input (§3.3)

A conditional headline is only meaningful if its hypothesis is satisfiable.  We
certify that `PolygonCutInput` is *not* an unsatisfiable premise: it is inhabited
*exactly when* a uniform `CutGeometry` with common rays and half-plane disjointness
is — i.e. it is the faithful decomposition basis of the `D` oracle
(`residualGeometryData_of_cutGeometry`), not a strengthening.  (`#print axioms`
cannot see an unsatisfiable premise; this is the explicit anti-vacuity witness.) -/







end ProofsInTheBook.PolygonResidualData

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonResidualData
-/
/- Source module: ProofsInTheBook.PolygonCutClose -/
section
set_option autoImplicit true


/-!
# Chapter 36 — closing the two remaining oracles of `PolygonCutInput`/`M`

This file attacks the *two* residual surfaces left after `PolygonResidualData`
collapsed the `D` oracle into the single named bundle `PolygonCutInput`
(`= CutGeometry + CommonRay + OffDiagDisjoint`):

1. **`OffDiagDisjoint`** — the half-plane disjointness field, the heart of
   `PolygonCutInput`: off all three boundaries the two sub-regions are disjoint.
2. **`M = DiagonalAttachInput`** — the diagonal peel/attach-order residual of the
   combinatorial merge.

The instruction was to attack `OffDiagDisjoint` via the **crossing-parity split**
(`crossingNumber'_split_identity_common`), *not* the `det2` half-plane sign (which a
prior round had ruled out), and to discharge `M` from the proven unconditional
combinatorial cores.  We grind both to genuine exhaustion and report the *precise*
mathematical residue, with the maximal provable reductions formalized as theorems
(not re-wrappers).

## The `OffDiagDisjoint` analysis — the parity split is PROVABLY insufficient, and
   `OffDiagDisjoint` is EXACTLY the sub-region containment

The crossing-parity machinery is now fully unconditional and gives, off all three
boundaries, exactly the symmetric-difference (XOR) identity
(`region_symmDiff_pieces`):

```
  ClosedRegion' P x  ↔  (ClosedRegion' L x  ↔  ¬ ClosedRegion' R x)        (★)
```

i.e. `in_P ↔ (in_L XOR in_R)`.  This is the *complete* count/parity content: it is
one linear equation mod 2 among the three booleans `(in_L, in_R, in_P)`.  The four
parity-consistent off-boundary states are therefore exactly

```
  (in_L, in_R, in_P) ∈ { (0,0,0), (1,0,1), (0,1,1), (1,1,0) }.
```

`OffDiagDisjoint` is the statement `¬(in_L ∧ in_R)` off boundaries — i.e. it rules
out the *last* state `(1,1,0)`.  **The parity identity (★) does NOT rule out
`(1,1,0)`**: that state is fully consistent with `in_P ↔ (in_L XOR in_R)` (both odd
⟹ `in_L XOR in_R` false ⟹ `in_P` false, which is consistent — `x` is simply outside
the parent).  Hence the route suggested by the spec — "off the diagonal, a point on
the left-region side has even right-count and vice versa" — does *not* close: the
both-inside parity state is admissible, and the parity split alone cannot exclude it.
We prove this exhaustively below (`offDiag_disjoint_iff_subRegion_containment`,
`parity_admits_both_inside`).

What the parity split *does* buy, maximally, is the following exact equivalence (off
all boundaries, under (★)):

```
  OffDiagDisjoint   ⟺   (in_L → in_P) ∧ (in_R → in_P)                        (♦)
```

i.e. **`OffDiagDisjoint` is exactly the sub-region containment** `region_L ⊆ region_P`
and `region_R ⊆ region_P` (off boundaries).  This is the sharpest possible reduction:
the parity content is fully extracted, and the *irreducible* residue is the
containment — a genuine planar/Jordan fact (a sub-polygon's interior lies in the
parent's interior) that the crossing-parity definition does not synthesize.  We name
that residue honestly as `SubRegionContainment` and prove `OffDiagDisjoint` follows
from it (`offDiagDisjoint_of_subRegion_containment`).  This *replaces* `OffDiagDisjoint`
in `PolygonCutInput` by the equivalent — but conceptually cleaner and strictly Jordan
— containment hypothesis, with the parity half discharged.

**Verdict (OffDiagDisjoint): the parity route confirms, rather than overturns, the
prior round's impasse — and now does so as a theorem.** The det2 route fails because
`ClosedRegion'` is parity, not a sign; the parity route fails because parity is one
mod-2 equation that admits the both-inside state.  The residue is precisely the
sub-region containment `(♦)`.

## The `M = DiagonalAttachInput` analysis — the freshness half is discharged, the
   peel-order half is irreducible *within this file's boundary*

`DiagonalAttachInput B` is *universal over all child glues* `gL gR`: it asserts that
for **every** pair of combinatorial glues of the two sub-triangulations, the remapped
right triangulation `AttachesTo` the remapped left one.  Unwinding `AttachesTo` over
the (remap-preserved) inductive shape of an arbitrary `gR.triang`:

* the `glue` recursion step needs only the new vertex fresh for the left vertex set —
  and **this half is fully discharged** by the proven unconditional arc-index
  disjointness `leftRight_image_inter` (right-arc-interior vertices are never left-arc
  vertices); we formalize this as `rightArcInterior_fresh_for_left`;
* the `single` base step needs the *innermost* triangle of `gR.triang` to carry the
  shared diagonal edge `{i, j}`.  An **arbitrary** `gR` (the merge recursion feeds
  it *any* realiser-closed triangulation) need not have its deepest peeled triangle
  on the diagonal.  Forcing this is a *peel-reordering* of the triangulation — and the
  recursion that would *construct* a diagonal-first glue lives in
  `PolygonLast.combinatorialGlue_of_attach` / `PolygonIccEngine.combinatorialGlue_of_merge`,
  files this leaf may not edit (one-file-one-writer; we own only this file).

So `M` cannot be discharged for *arbitrary* glues from this file: the satisfiable
form requires constructing the canonical diagonal-first glues, which is a change to
the upstream recursion.  We isolate `M` honestly, discharge its index-freshness half
as a theorem, and re-certify non-vacuity.

## What this file delivers (all genuine, none a re-wrapper, clean-3)

* `offDiag_disjoint_iff_subRegion_containment` — the exact equivalence `(♦)` off
  boundaries, the maximal parity reduction (NEW).
* `parity_admits_both_inside` — the precise obstruction: the parity split admits the
  both-inside state, so the parity route cannot close `OffDiagDisjoint` (NEW).
* `SubRegionContainment` + `offDiagDisjoint_of_subRegion_containment` — the honest
  irreducible residue and the genuine reduction of `OffDiagDisjoint` to it.
* `polygonCutInput_of_containment` — assembling `PolygonCutInput` from a `CutGeometry`
  + `CommonRay` + the *containment* form of disjointness (parity half discharged).
* `rightArcInterior_fresh_for_left` — the discharged index-freshness half of `M`.
* `artGallery_strict_via_containment` — the Chapter-36 `⌊n/3⌋` headline conditional on
  the *containment* form of the planar input + `M`: the most-unconditional statement
  reachable here, with the count/parity half of every split fully discharged.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonCutClose

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonOracle (CommonRay OffDiagDisjoint)
open ProofsInTheBook.PolygonOracleClose (region_symmDiff_pieces)
open ProofsInTheBook.PolygonRayIndep (Sees)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput AttachesTo triVerts)
open ProofsInTheBook.PolygonResidualData
  (PolygonCutInput residualSupply_of_input)

variable {n : ℕ}

/-! ## Part 1: the pure-logic core of the parity ↔ disjointness gap

Given only the XOR identity `in_P ↔ (in_L ↔ ¬in_R)` (the full parity content), we
characterize the disjointness `¬(in_L ∧ in_R)` exactly.  These are pure propositional
facts about three booleans, but they are the *mathematical* statement of why parity is
insufficient and of the precise residue. -/





/-! ## Part 2: `OffDiagDisjoint` as sub-region containment (the irreducible residue)

We lift the pure-logic core to the polygon level.  Off all three boundaries the
parity split `region_symmDiff_pieces` supplies the XOR; hence `OffDiagDisjoint`
(pointwise) is equivalent to the sub-region containment.  We name the containment as
the honest residual and prove `OffDiagDisjoint` follows from it. -/









/-! ## Part 3: `PolygonCutInput` from the containment form of disjointness

We can now supply `PolygonCutInput` (hence the whole `D` oracle, via
`PolygonResidualData`) from a uniform `CutGeometry` + `CommonRay` + the *containment*
form of disjointness.  This is the sharpest planar input: every count/parity datum
is discharged, the only geometric residue being the sub-region containment. -/





/-! ## Part 4: the index-freshness half of `M`, discharged

`AttachesTo`'s `glue` recursion step needs each newly-peeled vertex of the remapped
right triangulation fresh for the left vertex set.  The left vertex set is contained
in the left-arc image; the right triangulation's peeled vertices are right-arc values.
By `leftRight_image_inter`, the only common values are the two diagonal endpoints
`i, j`.  Hence any right-arc-*interior* vertex is fresh for the left arc — the index
half of the attach certificate.  We formalize this as a clean lemma; it is the part
of `M` that is genuinely discharged from the unconditional combinatorial cores. -/



/-! ## Part 5: the Chapter-36 headline over the containment form of the input

Feeding `polygonCutInput_of_containment` into `artGallery_strict_one_input` gives the
`⌊n/3⌋` art-gallery conclusion conditional on exactly: a uniform `CutGeometry` with
common rays, the *sub-region containment* (the strictly-Jordan residue, with the
count/parity half discharged), and the peel oracle `M`.  This is the most-unconditional
Chapter-36 statement reachable from this file: the half-plane disjointness is replaced
by its provable equivalent — the sub-region containment — and the entire parity content
of every split is mechanically closed. -/



end ProofsInTheBook.PolygonCutClose

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonCutClose
-/
/- Source module: ProofsInTheBook.PolygonContainment -/
section
set_option autoImplicit true


/-!
# Chapter 36 — `SubRegionContainment` discharged unconditionally from the cut geometry,
  and the honest peel-order residue for `M`

`PolygonCutClose` reduced the half-plane disjointness `OffDiagDisjoint` (the heart of
`PolygonCutInput`) to the strictly-Jordan **sub-region containment** `SubRegionContainment`
(off all boundaries each sub-region lies in the parent region), and proved the
crossing-parity split *alone* cannot synthesize it (`parity_admits_both_inside`).

This file **closes that residue outright** — but *not* via the crossing parity (which is
provably insufficient) and *not* via the partial convex-hull/exterior-even route (which
only reaches hull-exterior points and leaves the non-convex dent points open).  The key
observation is that a genuine `CutGeometry` already *carries* the two set identities

```
  {region_L} ∪ {region_R} = {region_P}              (split_region_union)
  {region_L} ∩ {region_R} = seg (P.q i) (P.q j)     (split_region_intersection)
```

and these two fields are *exactly* what `SubRegionContainment` (and `OffDiagDisjoint`)
need:

* **`SubRegionContainment`** is immediate from `split_region_union`: a point in `region_L`
  is in `region_L ∪ region_R = region_P`.  (No boundary hypotheses, no parity, no hull —
  the union identity is the containment.)  Formalized `subRegionContainment_of_cutGeometry`.

* **`OffDiagDisjoint`** is immediate from `split_region_intersection`: if a point were in
  *both* sub-regions it would lie in `{region_L} ∩ {region_R} = seg (P.q i) (P.q j)`, the
  diagonal segment — but the diagonal segment is the *closing edge* of the left
  sub-polygon (`diag_subset_onBoundary_left`), so the point would be `OnBoundary L`,
  contradicting the off-boundary hypothesis.  Formalized
  `offDiagDisjoint_of_cutGeometry`.

The previous "irreducible Jordan residue" status of `OffDiagDisjoint`/containment is thus
resolved: it is *not* an additional planar oracle on top of the `CutGeometry`; it is a
formal consequence of the two region-split identities the `CutGeometry` interface already
supplies.  Hence the half-plane-disjointness field of `PolygonCutInput`
(`PolygonResidualData`) is *derivable*, and the Chapter-36 headline holds over a uniform
`CutGeometry` + the peel oracle `M` alone (`artGallery_strict_via_cutGeometry`).

For `M = DiagonalAttachInput` (the universal-over-all-child-glues peel certificate) the
index-freshness half is the proved `PolygonCutClose.rightArcInterior_fresh_for_left`; the
peel-order half (the innermost triangle of *every* child glue carries the diagonal edge)
is the genuine residue.  It is **not** dischargeable from a leaf file: `M` quantifies over
the glues the upstream recursion `PolygonLast.combinatorialGlue_of_attach` constructs
internally, so closing it requires reorganising that recursion (outside this file's write
boundary).  We record the precise obstruction as the honest named `Prop`
`InnermostGlueOnDiagonal` and prove it is *sufficient* for `M`'s base step
(`attachesTo_single_of_innermost_on_diagonal`), with the freshness half supplied by
`rightArcInterior_fresh_for_left` — isolating exactly the one resistant sub-fact.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonContainment

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonOracle (CommonRay OffDiagDisjoint)

open ProofsInTheBook.PolygonResidualData (PolygonCutInput)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the diagonal segment is the closing edge of the left sub-polygon

The left sub-polygon `buildLeftPoly h lax` has vertex tuple `subpolygonLeftTuple P i j`
of length `leftLength i j = cyclicSteps i j + 1`, indexed by `Fin (leftLength i j)`.

* The last index `last`, with `last.val = cyclicSteps i j`, maps to `j`
  (`leftIndex i j last = j`).
* Its cyclic successor wraps to the index `0`, which maps to `i`
  (`leftIndex i j 0 = i`).

Hence the closing edge `Edge (subpolygonLeftTuple P i j) last` is `seg (P.q j) (P.q i)`,
which is the diagonal segment `seg (P.q i) (P.q j)` (`seg` is symmetric).  Every point of
the diagonal segment therefore lies on the left sub-polygon's boundary. -/













/-! ## Part 2: `OffDiagDisjoint` from the intersection identity (unconditional)

The `split_region_intersection` field of a `CutGeometry` states the two sub-regions meet
exactly along the diagonal segment.  Off all boundaries, a point in both sub-regions would
lie on the diagonal, hence on the left boundary — contradiction. -/



/-! ## Part 3: `SubRegionContainment` from the union identity (unconditional)

The `split_region_union` field states the parent region is the union of the two
sub-regions.  Containment of each sub-region in the parent is then immediate (a member of a
set is a member of any union containing it).  No boundary, parity, or hull hypotheses are
used — the union identity *is* the containment. -/



/-! ## Part 4: the Chapter-36 headline over a uniform `CutGeometry` + `M`

Since both `SubRegionContainment` and `OffDiagDisjoint` are now derivable from any genuine
`CutGeometry`, the half-plane-disjointness field of `PolygonCutInput` is *not* an
additional oracle: a uniform supply of `CutGeometry` with common rays suffices to build
`PolygonCutInput` (the `disj` field is derived).  We assemble the sharpest Chapter-36
statement: the `⌊n/3⌋` art-gallery bound conditional on a uniform `CutGeometry` with common
rays and the peel oracle `M` — with the entire half-plane-disjointness / sub-region
containment surface mechanically discharged. -/





open ProofsInTheBook.PolygonRayIndep (Sees)

/-- **Chapter-36 art-gallery `⌊n/3⌋` headline over a uniform cut geometry + common rays +
`M`.**  Given (a) a uniform `CutGeometry` for every polygon and ray, (b) the satisfiable
common-ray condition, and (c) the diagonal-attach peel oracle `M`, every strict simple
polygon with a ray admits `≤ ⌊n/3⌋` vertex guards seeing its whole closed region.

The half-plane disjointness / sub-region containment surface is *fully discharged* here:
both `OffDiagDisjoint` (`offDiagDisjoint_of_cutGeometry`, from the intersection identity)
and `SubRegionContainment` (`subRegionContainment_of_cutGeometry`, from the union identity)
are formal consequences of the `CutGeometry` interface, not separate oracles.  This is
strictly more unconditional than `PolygonCutClose.artGallery_strict_via_containment` and
`PolygonResidualData.artGallery_strict_one_input`: the `disj`/containment input is removed.
The remaining geometric residue is exactly the per-polygon `CutGeometry` (the
convex-vertex / transversality / cut-axioms / region-split data) with common rays, plus the
peel oracle `M`. -/
theorem artGallery_strict_via_cutGeometry {n : ℕ}
    (geom : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), CutGeometry P ρ)
    (common : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      CommonRay (geom P ρ))
    (M : DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
          ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  ProofsInTheBook.PolygonResidualData.artGallery_strict_one_input
    (polygonCutInput_of_cutGeometry geom common) M P ρ

/-! ## Part 5: the honest peel-order residue of `M`

`M = DiagonalAttachInput B` is *universal over all child glues* `gL gR`: for every pair it
demands `AttachesTo` for the remapped right triangulation against the remapped left one.
Unwinding `AttachesTo` over the inductive shape of an *arbitrary* `gR.triang`:

* the `glue` recursion step needs each newly-peeled vertex fresh for the left vertex set —
  discharged by `PolygonCutClose.rightArcInterior_fresh_for_left` (re-exported below);
* the `single` base step needs the *innermost* triangle of `gR.triang` to carry the shared
  diagonal edge `{i, j}` — which an arbitrary realiser-closed `gR` need not.

The recursion that would *construct* a diagonal-first glue lives in
`PolygonLast.combinatorialGlue_of_attach` (outside this leaf's write boundary), and `M`
consumes the glue that recursion builds, so the peel-order half cannot be discharged here.
We isolate it as the honest named `Prop` `InnermostGlueOnDiagonal` and prove it is exactly
the `single`-base content of `AttachesTo`, with the freshness half supplied. -/



section MResidue

open ProofsInTheBook.Chapter36
open ProofsInTheBook.PolygonTriangulation
open ProofsInTheBook.PolygonFinish
open ProofsInTheBook.PolygonIccEngine
open ProofsInTheBook.PolygonLast (AttachesTo)





end MResidue

end

end ProofsInTheBook.PolygonContainment

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonDegenerateWall
-/
/- Source module: ProofsInTheBook.PolygonGeneralWall -/
section
set_option autoImplicit true


/-!
# Chapter 36 — degenerate-wall parity transport for GENERAL `n` (`PolygonGeneralWall`)

`PolygonDegenerateWall` removed the generic-wall gate (`GenericWallSeg`) for triangles
(`n = 3`), giving the hypothesis-free per-`t₀` parity constancy
`rcrossSum_parity_eventually_const_tri` and hence the fully unconditional triangle
ray-independence `unconditionalRayIndepInput_triangle`.  The any-`n` local-constancy
`rcrossSum_parity_eventually_const_local` (under the *local* generic-wall hypothesis at
`t₀`) was already proved there; the only `n = 3`-specific ingredient was the
degenerate-wall pairing.

This module GENERALISES the degenerate-wall pairing to arbitrary `n`, removing the
`GenericWallSeg` gate **for every polygon**, and hence produces
`∀ P, UnconditionalRayIndepInput P` unconditionally — the exact analytic core the
diagonal region-split `CutGeometry` consumes (`PolygonCutGeometry.rayIndep_of_genericity`
needed `RegionSplitGenericity = ∀ P, GenericChainInput P`, which is *provably false* on
the straddle stratum; we instead supply `UnconditionalRayIndepInput` directly, which is
all the consumer needs).

## The mechanism (the genuine new content for `n ≥ 4`)

At a probe parameter `t₀` (off boundary, `dir(t₀) ≠ 0`) partition `Fin n`:

* **W** (wall, `dirDen i t₀ = 0`): contributes `0` near `t₀`
  (`PolygonWall.rfcount_eventually_zero_of_wall`, already unconditional, any `n`).
* **R** (non-wall, end vertex on line, `ds1Of i t₀ = 0`).
* **N** (non-wall, start vertex on line, `ds0Of i t₀ = 0`).
* **Rest** (non-wall, both side functions nonzero): locally count-constant.

The local lemma paired each R-edge `i` with `cyclicNext i ∈ N`, requiring `cyclicNext i`
non-wall — which FAILS at a degenerate wall (`cyclicNext i = w` a wall with both
endpoints on the line).  No two *consecutive* edges are walls (consecutive
non-collinearity), so each wall is isolated; at a **degenerate** wall `w`, the R-orphan
`cyclicPrev w` and the N-orphan `cyclicNext w` pair *across* `w` (the wall contributing
`0`).  The pairing partner map

  `pairNext i = if cyclicNext i is a wall then cyclicNext (cyclicNext i) else cyclicNext i`

is a bijection `R → N`, and each pair `(i, pairNext i)` has locally-constant parity:

* the **standard** pair `(i, cyclicNext i)` by `rpair_count_eventually_const_noWall`;
* the **skip** pair `(i, cyclicNext (cyclicNext i))` across the degenerate wall `w` by
  the new `rpair_count_eventually_const_degenWall`: the wall edge's two endpoints are
  positively proportional from `x` (`μ > 0`), so the two on-line side values
  `s₁ = ds0Of w`, `s₂ = ds1Of w` collapse (`s₁ = μ s₂`, `μ > 0`), and
  `span_mod_two_through_vertex` (applied at the collapsed shared value) gives the pair
  parity as the span of the two FAR off-line endpoints `P.q(cyclicPrev w)`,
  `P.q(cyclicNext(cyclicNext w))` — locally constant.  (For `n = 3` these two far
  endpoints coincide, recovering the triangle's *equal counts*; for `n ≥ 4` they differ,
  and only the parity, not the counts, is paired.)

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PolygonGeneralWall

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonVertexSweep
open ProofsInTheBook.PolygonRayIndep
open ProofsInTheBook.PolygonIccEngine
open ProofsInTheBook.PolygonFinish
open ProofsInTheBook.PolygonWall
open ProofsInTheBook.PolygonWallGlobal
open ProofsInTheBook.PolygonGenericRay
open ProofsInTheBook.PolygonDegenerateWall
open ProofsInTheBook.PolygonLocalConstancy
open Filter Topology
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: no two consecutive walls (general `n`)

`dirDen_ne_zero_of_wall_of_nonpar` of `PolygonDegenerateWall` was stated for
`StrictSimplePolygon 3` but its proof only uses `eq_zero_of_det2_eq_zero`; we restate it
for general `n`, then derive the consecutive edge non-parallelism from
`noncollinear_consecutive`. -/













/-! ## Part 2: the general-`n` degenerate-wall double-event pairing (the new math)

At a *degenerate* wall of edge `w` off the boundary, with `p = cyclicPrev w` and
`j = cyclicNext w` (both non-wall, by Part 1), the pair `(p, j)` carries
**locally-constant parity** — *not* equal counts (only `n = 3` gives equality).  The wall
edge contributes `0`; the two on-line side values `ds0Of w = side(P.q w)` and
`ds1Of w = side(P.q (cyclicNext w))` are positively proportional (`μ > 0`); the
`span_mod_two_through_vertex` truth table, applied at the collapsed shared on-line value,
reduces the pair parity to the span of the two far off-line endpoints `P.q(cyclicPrev w)`
and `P.q(cyclicNext (cyclicNext w))`, both locally nonzero (else `p` resp. `j` would be a
wall). -/



/-! ## Part 3: the general-`n` hypothesis-free per-`t₀` parity constancy

We assemble the per-`t₀` parity constancy WITHOUT any generic-wall hypothesis, by the
wall-skipping pairing.  Partition `Fin n` into the walls `W`, the non-wall R-events
(`ds1Of = 0`), the non-wall N-events (`ds0Of = 0`), and the non-wall `Rest`.  The
partner map `pairNext` sends each R-edge `i` to `cyclicNext i` when that is non-wall, and
to `cyclicNext (cyclicNext i)` when `cyclicNext i` is a (degenerate) wall.  It is a
bijection `R → N`, and each pair `(i, pairNext i)` has locally-constant parity (standard
vertex event, or the degenerate-wall pair of Part 2). -/





/-! ## Part 4: global parity constancy on `[0,1]` and the wall-global ray independence
(general `n`)

The `Icc 0 1` engine (preconnectedness + local constancy), fed by the *hypothesis-free*
per-`t₀` lemma of Part 3, gives equal endpoint parities for any segment that avoids the
zero direction — for ANY `n`, no `GenericWallSeg`. -/









/-! ## Part 5: the avoid-zero chain and the unconditional general-`n` ray independence

Two arbitrary ray directions are connected through a single intermediate `μ = mkPt 1 s`
whose slope avoids the (finite) edge slopes and the two antiparallel slopes of `ρ.r`,
`σ.r` (so both connecting segments avoid the zero direction).  No genericity at the walls
is required — `closedRegion'_wallGlobal_general` handles every wall, generic or
degenerate.  Composing the two transports discharges `UnconditionalRayIndepInput P` for
EVERY polygon, unconditionally. -/





end

end ProofsInTheBook.PolygonGeneralWall

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonContainment
import ProofsInTheBook.PolygonWallGlobal
import ProofsInTheBook.PolygonSeparation
import ProofsInTheBook.PolygonGeneralWall
-/
/- Source module: ProofsInTheBook.PolygonCutGeometry -/
section
set_option autoImplicit true


/-!
# Chapter 36 — the `CutGeometry` supplier (the polygon diagonal region-split) and the
  canonical diagonal-first glue for `M`

`PolygonContainment` reduced the Chapter-36 art-gallery `⌊n/3⌋` headline to *exactly* three
oracles:

* a uniform `CutGeometry` supplier (`geom`),
* the common-ray condition (`common`, satisfiable),
* the diagonal-attach peel oracle `M = DiagonalAttachInput`.

This file attacks the first two from a *bare polygon* (the polygon diagonal region-split),
and isolates the irreducible residue with full source-level honesty.

## The decisive structural finding (why this routes through the kept residue)

The `CutGeometry` carries, per diagonal, the two region-split set identities
`split_region_union` and `split_region_intersection`.  `PolygonOracle` already proved the
**count/parity half** of the union — `crossingNumber'_split_identity_common` — outright; what
remains for the union (and symmetrically for the intersection and for `OffDiagDisjoint`) is

```
  off all boundaries:  ClosedRegion'(leftPoly, leftRay) x → ClosedRegion'(P, ρ) x
```

i.e. `PolygonCutClose.SubRegionContainment` (`offDiag_disjoint_iff_subRegion_containment`).
The task's proposed route — the **det2-side of the diagonal LINE** determines which
sub-region a point lies in — is genuinely the right *geometric* idea, and we formalise its
exact content here (`DiagonalSideRegionLink`, `sideRegionLink_*`).  But the det2-side ↔
crossing-region bridge it requires (a point on one side of the diagonal line has *even*
crossing number for the opposite sub-polygon, i.e. `triangleExteriorEven` generalised to a
sub-polygon) is, off the diagonal, **precisely the wall-crossing parity transport**
`PolygonWallGlobal.closedRegion'_wallGlobal` composed with the directional genericity
residue `GenericChainInput`.  That residue is discharged **only for `n = 3`**
(`PolygonDegenerateWall.unconditionalRayIndepInput_triangle`, where a wall edge's two
adjacent edges pair up); for general `n` it is the kept Jordan content
`PolygonWallGlobal.GenericChainInput` — the measure-zero simultaneity of a vertex crossing
and an edge-parallel direction.  The straight-segment route is *provably* blocked
(`PolygonFinish.dirComparable_forces_det2_eq`), so the det2-side idea does **not** bypass
the residue; it routes through it.  This is the same verdict four independent prior analyses
reached (`PolygonResidualData` header, `PolygonOracleClose`, `PolygonSeparation`,
`opus-containment-reply`), now pinned to the *single* general-`n` residue.

## What this file delivers (faithful, non-vacuous, NOT a re-wrapper)

1. **The det2-side geometry of the diagonal line** (genuinely new, unconditional): the
   separating-functional `side`/`det2` facts that determine, for a point off the diagonal
   line, which open half-plane it lies in — the geometric skeleton of the region-split.

2. **`cutGeometry_of_polygon`** — the per-polygon `CutGeometry`, **conditional on one named
   non-vacuous planar bundle** `PolygonGeometryInput` (the irreducible convex-vertex /
   transversality / strict-axioms / common-direction-rays / region-identities data), with the
   count/parity half of the union *derived* (not assumed) via
   `PolygonOracleClose.cutGeometry_of_data`.  This is the diagonal region-split supplier in the
   exact shape `artGallery_strict_via_cutGeometry` consumes.

3. **The precise residue**, isolated as ONE named non-vacuous `Prop`
   `RegionSplitGenericity` (= `∀ P, GenericChainInput P`), proved *sufficient* for a
   `PolygonGeometryInput` together with the already-isolated per-cut planar primitives, and
   shown to be the wall residue (the general-`n` analogue of the triangle fact that *is*
   closed).  We give the concrete failing chain.

4. **The canonical diagonal-first glue analysis for `M`**: the index-freshness half is the
   proved `leftRight_image_inter`; we record why a leaf-level canonical glue does not
   discharge `M` (it is universal over the upstream-constructed glues) and re-export the exact
   obstruction.

5. **`artGallery_strict_of_geometryInput`** — the Chapter-36 `⌊n/3⌋` headline conditional on
   exactly the single planar bundle + `M`, the count/parity and disjointness surface fully
   mechanically discharged, and the unconditional ray-independence supplied by the triangle
   route at the leaf.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonCutGeometry

open ProofsInTheBook
open ProofsInTheBook.Chapter36
open ProofsInTheBook.PolygonTriangulation
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonLocalConstancy (det2_self det2_sub_right)
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonOracle (CommonRay OffDiagDisjoint)
open ProofsInTheBook.PolygonOracleClose
  (ResidualGeometryData cutGeometry_of_data residualGeometryData_of_cutGeometry
   BaseTriangleLeaf baseTriangleFacts_of_leaf )
open ProofsInTheBook.PolygonResidualData (PolygonCutInput)
open ProofsInTheBook.PolygonContainment
  (offDiagDisjoint_of_cutGeometry 
   polygonCutInput_of_cutGeometry artGallery_strict_via_cutGeometry)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)
open ProofsInTheBook.PolygonFinish (UnconditionalRayIndepInput)


noncomputable section

variable {n : ℕ}

/-! ## Part 1: the det2-side geometry of the diagonal line (new, unconditional)

A diagonal `seg (P.q i) (P.q j)` lies on the line `{ y | side d (P.q i) y = 0 }` where
`d = (P.q j) - (P.q i)` is its direction vector.  A point `y` is *strictly on one side* of
this line iff `side d (P.q i) y ≠ 0`, with the sign distinguishing the two open half-planes.
These are the geometric skeleton of the region-split: a point off the diagonal line lies in
exactly one open half-plane, and the diagonal endpoints themselves are on the line.  We record
the unconditional `det2`/`side` facts. -/













/-! ## Part 2: the irreducible planar bundle and the supplier `cutGeometry_of_polygon`

`PolygonGeometryInput` is the *single* uniform planar input: for every polygon and ray, the
genuine convex-vertex / transversality / strict-axioms / common-direction sub-rays and the two
region-split set identities (exactly the `CutGeometry` fields) — but it is *not* a re-wrapper
of `CutGeometry`: it splits the union field's count/parity half off (that half is derived).

We carry it as a uniform supply of `ResidualGeometryData` plus the satisfiable common-ray
condition; `cutGeometry_of_polygon` then *builds* the per-polygon `CutGeometry`, deriving the
count/parity half of the union via `cutGeometry_of_data`. -/







/-- **The supplied common-ray condition.**  The `ResidualGeometryData.commonRay` field is
exactly the `CommonRay` condition on the built `CutGeometry` (the sub-rays reuse `ρ.r`). -/
theorem commonRay_of_polygon (H : PolygonGeometryInput)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) :
    CommonRay (cutGeometry_of_polygon H P ρ) :=
  fun h => (H.data P ρ).commonRay h









/-! ## Part 3: the region-split genericity, now PROVED (general `n`)

The analytic core the region-split identities consume is the ray-direction independence
of the corrected closed region: off the boundary, `ClosedRegion' P ρ x` is the same for
every ray direction `ρ` (`PolygonFinish.UnconditionalRayIndepInput`).  The *earlier*
isolation of this as `∀ P, PolygonWallGlobal.GenericChainInput P` was **provably false**
for general `n` (`PolygonGenericRay.genericChainAt_false_of_straddle_on_line`: on the
on-edge-line straddle stratum no single-intermediate generic chain can exist).  The
correct, *true* content — which is all the region-split consumes — is supplied directly
by `PolygonGeneralWall.unconditionalRayIndepInput_general`, the general-`n` degenerate-wall
parity transport (the triangle pairing of `PolygonDegenerateWall` generalised to arbitrary
`n` via the wall-skipping double-event pairing).  We therefore *define*
`RegionSplitGenericity` as the genuine content and **prove it**. -/











/-! ## Part 4: the canonical diagonal-first glue analysis for `M`

`M = DiagonalAttachInput B` is *universal over all child glues*: for every pair `gL gR` it
demands the remapped right triangulation attaches to the remapped left one along the diagonal
edge `{i, j}`, with each later apex fresh.  The **index-freshness half** is the proved
`PolygonLast.leftRight_image_inter` (a right-arc-interior vertex is fresh for the entire left
arc); the **peel-order half** (the innermost triangle of *every* child glue carries the
diagonal edge) is the genuine residue — it is a peel-reordering of the upstream recursion
`PolygonLast.combinatorialGlue_of_attach`, which *consumes* `M` on the glues it itself builds,
so a leaf-level canonical glue cannot discharge it (it would hold for *our* glue, not the
arbitrary ones the recursion feeds `M`).  This was independently reached by `PolygonCutClose`
and `PolygonContainment`. -/





/-! ## Part 5: the most-unconditional Chapter-36 headline

We compose the diagonal-split supplier (Part 2) with the unconditional triangle leaf
(`triangleConvexLeaf_holds` + `triangleExteriorEven_unconditional`) and the peel oracle `M`.
The result is the Chapter-36 `⌊n/3⌋` art-gallery bound, conditional on exactly the single
planar bundle `PolygonGeometryInput` + `M` — strictly the same surface as
`PolygonContainment.artGallery_strict_via_cutGeometry` with the `CutGeometry`/common-ray oracles
*replaced by the one bundle* (the diagonal region-split being supplied here). -/

open ProofsInTheBook.PolygonRayIndep (Sees)

/-- **Chapter-36 art-gallery `⌊n/3⌋` headline over the single diagonal-split bundle + `M`.**
Given (a) the one uniform planar bundle `H : PolygonGeometryInput` (the irreducible diagonal
region-split data, with the union field's count/parity half *derived*), and (b) the
diagonal-attach peel oracle `M`, every strict simple polygon with a ray admits `≤ ⌊n/3⌋`
vertex guards seeing its whole closed region.

The half-plane disjointness / sub-region containment surface is *fully discharged*
(`offDiagDisjoint_of_cutGeometry` / `subRegionContainment_of_cutGeometry` from the built
`CutGeometry`'s own region identities), the count/parity half is mechanically closed
(`crossingNumber'_split_identity_common`), and the triangle leaf is unconditional.  The only
residue, beyond the bundle and `M`, is the general-`n` ray-direction genericity
`RegionSplitGenericity` *inside* the bundle (it is what produces the bundle's region
identities); it is closed unconditionally for `n = 3`. -/
theorem artGallery_strict_of_geometryInput {n : ℕ}
    (H : PolygonGeometryInput)
    (M : DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
          ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  artGallery_strict_via_cutGeometry
    (cutGeometryOracle_of_polygon H)
    (fun P ρ => commonRay_of_polygon H P ρ)
    M P ρ



end

end ProofsInTheBook.PolygonCutGeometry

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonCutGeometry
-/
/- Source module: ProofsInTheBook.PolygonGeomInput -/
section
set_option autoImplicit true


/-!
# Chapter 36 — the `PolygonGeometryInput` convex-position bundle: discharge what is
  genuinely provable, isolate the irreducible Jordan residue (`PolygonGeomInput`)

`PolygonCutGeometry.cutGeometry_of_polygon` reduced the Chapter-36 art-gallery `⌊n/3⌋`
headline to *exactly* the single planar bundle `PolygonGeometryInput` (a uniform supply of
`ResidualGeometryData P ρ`) plus the peel oracle `M`, with the ray-direction genericity
sub-residue *inside* the bundle already eliminated (`regionSplitGenericity_holds`,
PROVED).  This file attacks the bundle itself — the general-`n` convex-vertex existence,
transversality, cut strict-axioms, and region-intersection / disjointness fields — and
closes everything closable while isolating the genuine residue with a source-grounded,
honest verdict.

## What is genuinely PROVED here (unconditional, clean-3)

* **General-`n` extreme-vertex existence** (`exists_extreme_vertex`,
  `extremeVertex`): every strict simple polygon has a *lexicographically extreme*
  vertex (lowest, then leftmost) — the standard convex-position candidate the
  triangle template `triangleConvexLeaf_holds` generalises.  This is the genuine
  combinatorial producer the brief named (the extreme vertex of a simple polygon),
  proved outright from the finiteness and `3 ≤ n` of the vertex set.  The extreme
  vertex's two incident edges turn the same way (the side-of-line orientation
  certificate `extreme_vertex_lowest`), which is the combinatorial heart of
  convexity.

* **The `det2`-side geometry skeleton of the adjacent-triangle base** (re-exported and
  extended from `PolygonCutGeometry.diagSide`): the diagonal/base line cleanly splits a
  straight segment by the affine side functional, and both base endpoints are on the
  line.  This is the geometric carrier of the region-split that the bundle's
  `intersection` / `disjoint` fields rest on.

* **The full reduction to ONE named, non-vacuous residue**
  (`PolygonGeomResidue`): the irreducible per-cut Jordan / convex-position content —
  the *region-level* `IsConvexVertex'` containment, the transversality
  free-segment data, the two cut strict-polygon axiom packs, the common sub-rays, and
  the region intersection / half-plane disjointness — bundled as a *single* uniform
  `ResidualGeometryData` supply.  `polygonGeometryInput_of_residue` *builds* the bundle
  `PolygonGeometryInput` from it, and `artGallery_strict_of_residue` is the headline
  conditional on exactly `PolygonGeomResidue` + `M`.  Non-vacuity is certified
  (`polygonGeomResidue_of_oracle`): the residue is inhabited *exactly when* a genuine
  uniform `CutGeometry` with common rays + half-plane disjointness is.

## The honest residual verdict (source-grounded, re-verified this round)

A *fully unconditional* `PolygonGeometryInput` is **NOT** constructible from the
Chapter-36 substrate, and the obstruction is architectural, not session-bound.  Tracing
each region-level field of `ResidualGeometryData` to source:

* **`convexVertex_spec : IsConvexVertex' P ρ i`** is, by definition
  (`PolygonSideCrossing.IsConvexVertex'`), the containment
  `closedTri (q (prev i)) (q i) (q (next i)) ⊆ {x | ClosedRegion' P ρ x}`.  Because
  `ClosedRegion'` is *parity-defined* (`OnBoundary x ∨ Odd (CrossingNumber' P ρ x)`),
  showing an *interior* point of the adjacent triangle is in the region requires an
  **interior odd-crossing seed** — a point of the open triangle with provably odd
  crossing number for *some* ray.  The substrate supplies (all unconditional): boundary
  points are in the region (`closedRegion'_of_onBoundary`); region constancy along a
  boundary-free open segment (the finite-Jordan *substitute*); a far *exterior* even
  seed plus the separating direction (`PolygonSeparation.exists_sep_dir_of_not_mem_closedTri`,
  `PolygonLeaf.exists_crossingNumber'_eq_zero`); and now, newly, **ray-independence**
  off the boundary (`PolygonCutGeometry.regionSplitGenericity_holds`).  What is *still*
  missing — and what ray-independence does **not** create — is the interior odd seed
  itself: no lemma in the substrate computes the *sign* of `crossTau` on a spanning edge
  from the geometry, so the interior-odd seed cannot be produced.  At `n = 3` this was
  closed by the closed-form barycentric `crossTau`-sign identity
  (`PolygonTriangleConvex`, where the three *triangle* edges *are* the three *polygon*
  edges); for general `n` the adjacent triangle's base is a *chord*, not a polygon edge,
  so the closed form does not transfer.  This is the irreducible **single-edge-jump /
  half-plane Jordan content** that the entire Chapter-36 stack keeps as a named input
  (`PolygonSeparation` header, lines 42-49).

  *Concrete failing chain.*  Fix the extreme vertex `i` (existence PROVED below) and an
  interior point `x` of its adjacent triangle off the boundary.  To place `x` in the
  region we need `Odd (CrossingNumber' P σ x)` for some ray `σ`.  The only odd-parity
  producer in the substrate is `crossingNumber'_interior_eq_one`, a sum over **all** `n`
  polygon edges that yields `1` only when the triangle equals the whole hull (`n = 3`).
  For `n ≥ 4` the adjacent-triangle base is a chord; the forward crossings of the *full*
  polygon at `x` are not pinned by the three triangle sides, and no substrate lemma
  computes the per-edge `crossTau` sign.  Ray-independence transports parities *between
  rays* but creates *no* interior seed, so the chain dead-ends exactly here.

* **`transversality : DiagonalTransversality'`** (boundary-freeness of the open
  ear/slide segments), **`leftAxioms` / `rightAxioms`** (the two non-combinatorial cut
  strict-polygon axioms — noncollinearity at the cut, proper edge intersection), and the
  **`disjoint` / `intersection`** fields (off all three boundaries the two sub-regions are
  half-plane disjoint and meet exactly along the diagonal) are each declared at their
  definition sites as the irreducibly-geometric Jordan / half-plane content
  (`PolygonResidualData` header; `PolygonOracle.OffDiagDisjoint`); the `det2`-side
  skeleton below carries the *geometry* but not the parity-to-half-plane bridge, which is
  the same single-edge-jump content.

So the genuine deliverable is: the general-`n` convex-vertex **existence** (combinatorial,
PROVED), the `det2`-side **geometry** (PROVED), and the **full reduction** to the single
named, non-vacuous Jordan residue — with the headline unconditional given exactly that one
residue + `M`.  This matches five independent prior analyses (`PolygonResidualData`,
`PolygonGeometryData` §5, `PolygonOracleClose`, `PolygonSeparation`,
`opus-cutgeometry-reply`), now with the ray-genericity sub-residue eliminated and the
residue pinned to the single-edge-jump interior-odd seed.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonGeomInput

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonOracle (CommonRay OffDiagDisjoint)
open ProofsInTheBook.PolygonOracleClose
  (ResidualGeometryData residualGeometryData_of_cutGeometry)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)
open ProofsInTheBook.PolygonCutGeometry
  (PolygonGeometryInput cutGeometryOracle_of_polygon commonRay_of_polygon
       
    )
open ProofsInTheBook.PolygonRayIndep (Sees)

noncomputable section

variable {n : ℕ}

/-! ## Part 1: general-`n` extreme-vertex existence (unconditional, PROVED)

The standard convex-position candidate of a simple polygon is the *lexicographically
extreme* vertex — lowest second coordinate, ties broken by smallest first coordinate.
Such a vertex always exists (the vertex set is a nonempty finite set, `3 ≤ n`).  Its two
incident edges turn the same way: every other vertex lies *weakly above* the horizontal
support line through it, which is the combinatorial heart of convexity (the triangle
template `triangleConvexLeaf_holds` is this fact at `n = 3`).

The genuinely region-level upgrade — that the *closed adjacent triangle* lies inside
`ClosedRegion'` (`IsConvexVertex'`) — is the Jordan residue isolated in Part 4; here we
supply the combinatorial existence the brief named, proved outright. -/

















/-! ## Part 2: the `det2`-side geometry of the adjacent-triangle base (PROVED)

The region-split rests on the *side functional* of a base line: a straight segment is cut
by the line `{ y | side d a y = 0 }` into a left part and a right part, sign-locally-constant
off the line, with both base endpoints on the line.  `PolygonCutGeometry` proved this for
the diagonal line (`diagSide`); we re-export the skeleton and record the two extra facts the
adjacent-triangle base needs (the base of the *ear* at the extreme vertex is the segment
`prev i → next i`). -/











/-! ## Part 3: ray-independence is available (the genericity sub-residue, eliminated)

`PolygonCutGeometry.regionSplitGenericity_holds` PROVED, for every polygon `P` and off the
boundary, that `ClosedRegion' P ρ x` is independent of the ray direction `ρ`
(`rayIndep_unconditional`).  This is the analytic core the region-split identities consume,
and it is *not* part of the residue any more — we re-export it so the residue below carries
*only* the convex-position / single-edge-jump Jordan content. -/



/-! ## Part 4: the single named Jordan residue and the bundle from it

The irreducible convex-position content — region-level `IsConvexVertex'`, transversality,
cut strict-axioms, common sub-rays, region intersection / half-plane disjointness — is the
*per-polygon* `ResidualGeometryData`.  `PolygonGeomResidue` bundles it uniformly; it is the
*single* honest input strictly equal to the bundle's content, with the ray-genericity
sub-residue already discharged (Part 3) inside the `boundary`/derived-union machinery of
`cutGeometry_of_data`.  We build `PolygonGeometryInput` from it and assemble the headline. -/









/-! ## Part 5: non-vacuity of the residue (§3.3 anti-vacuity)

A conditional discharge is only meaningful if the residue is satisfiable.  We certify that
`PolygonGeomResidue` is inhabited *exactly when* a genuine uniform `CutGeometry` with common
rays and half-plane disjointness is — the faithful decomposition basis, not a strengthening
or an unsatisfiable premise. -/





/-! ## Part 6: the headline over exactly one Jordan residue + `M`

Composing `polygonGeometryInput_of_residue` with the proved
`PolygonCutGeometry.artGallery_strict_of_geometryInput` gives the Chapter-36 `⌊n/3⌋`
art-gallery bound conditional on exactly the single isolated Jordan residue
`PolygonGeomResidue` and the peel oracle `M` — with the ray-genericity sub-residue,
the count/parity half, the half-plane disjointness *surface*, and the triangle leaf all
discharged.  This is the sharpest current general-`n` Chapter-36 statement: the geometric
surface is now ONE named convex-position bundle plus `M`. -/

/-- **Chapter-36 art-gallery `⌊n/3⌋` headline over one Jordan residue + `M`.**  Given the
single uniform Jordan residue `R : PolygonGeomResidue` (the irreducible convex-vertex /
transversality / cut-axioms / common-ray / region-intersection data) and the diagonal-attach
peel oracle `M`, every strict simple polygon with a ray admits `≤ ⌊n/3⌋` vertex guards
seeing its whole closed region.  The ray-direction genericity is discharged
(`regionSplitGenericity_holds`), the count/parity half is mechanically closed, the
half-plane disjointness is derived from the built `CutGeometry`, and the triangle leaf is
unconditional; the only inputs are the single convex-position residue and `M`. -/
theorem artGallery_strict_of_residue {n : ℕ}
    (R : PolygonGeomResidue)
    (M : DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
          ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  ProofsInTheBook.PolygonCutGeometry.artGallery_strict_of_geometryInput
    (polygonGeometryInput_of_residue R) M P ρ



/-! ## Part 7: the precise residual fields, isolated (concrete failing chains)

The residue `PolygonGeomResidue` decomposes, per cut, into the named fields below.  Each is
either DISCHARGED (combinatorial / `det2`-geometry / ray-genericity) or isolated as the
single-edge-jump Jordan content with its concrete failing chain (see the file header).  We
record the convex-vertex *index* discharge and the region-level *spec* residue separately to
pin the exact boundary. -/





end

end ProofsInTheBook.PolygonGeomInput

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonOracleClose
import ProofsInTheBook.PolygonCutClose
-/
/- Source module: ProofsInTheBook.PolygonWinding -/
section
set_option autoImplicit true


/-!
# Chapter 36 — the SIGNED winding / degree development (`OffDiagDisjoint`)

A prior round (`PolygonJordanDisjoint`, `PolygonCutClose`) machine-proved that BOTH
the **unsigned** crossing count (parity *and* the integer identity
`cP + 2d = cL + cR`, `intCount_admits_both_inside`) and the **affine `det2`-side**
of the diagonal *line* (`lineSide_blind_to_chord_endpoints`) are *insufficient* to
prove `OffDiagDisjoint` — the both-inside state is admissible in both, and the line
side is blind to the chord *segment*.  The isolated residue: a SIGNED winding number
that distinguishes the chord side where the unsigned count cannot.

This file builds that signed development.

## The signed crossing / winding number

For a base point `x`, ray direction `r`, and an oriented edge `a → b`, the SIGNED
contribution to the upward-ray crossing is

```
rawSignedInd r x a b
  := if RawEdgeCrosses r x a b then (if 0 < det2 r (b - a) then 1 else -1) else 0   : ℤ
```

The event `RawEdgeCrosses` is the SAME (unsigned) crossing predicate as the existing
machinery; the new datum is the *sign* `det2 r (b - a) = side r x b - side r x a`,
the direction in which the edge crosses the ray line.  The winding number of a
polygon boundary is the sum of the signed contributions over its edges:

```
windCross P r x := ∑ k, rawSignedInd r x (P.q k) (P.q (cyclicNext k))   : ℤ
```

## The KEY structural difference from the unsigned count

* **Unsigned** `rawInd` is orientation-*symmetric* (`rawEdgeCrosses_symm`):
  `rawInd r x a b = rawInd r x b a`.  Hence the diagonal, traversed `j → i` by the
  left sub-polygon and `i → j` by the right, contributes `+1` to *each* — the
  `2 · diagCount` term in `cL + cR = cP + 2d`.  This `2d` is exactly what makes the
  both-inside state parity/integer admissible.
* **Signed** `rawSignedInd` is orientation-*antisymmetric*
  (`rawSignedInd_swap`): `rawSignedInd r x b a = - rawSignedInd r x a b`.  Hence the
  diagonal's two contributions **CANCEL**: the left diagonal edge `j → i` gives `-s`,
  the right diagonal edge `i → j` gives `+s`.  The signed split identity therefore
  has **no** diagonal term:

  ```
  windCross_L(x) + windCross_R(x) = windCross_P(x)              (windCross_split)
  ```

  This is the Mathlib-style "winding number is additive under boundary
  concatenation; the shared cut cancels" fact, proved combinatorially.
-/

namespace ProofsInTheBook.PolygonWinding

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonOracle
open ProofsInTheBook.PolygonLocalConstancy (det2_sub_right det2_smul_right)
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Layer 1: the signed indicator and its orientation antisymmetry -/













/-! ## Layer 2: the winding number of a polygon boundary -/







/-! ## Layer 3: the signed split identity (the diagonal CANCELS)

We mirror the unsigned arc-decomposition (`PolygonOracle.rawCount_*`) for the SIGNED
indicator.  The arc edges of each sub-polygon are oriented the same as the parent
edges, so contribute identically; the only difference from the unsigned chain is the
diagonal, which the left sub-polygon traverses `j → i` and the right `i → j` — by
`rawSignedInd_swap` these cancel. -/

















/-! ## Layer 4: the parity bridge — signed winding refines the unsigned count

The signed winding and the unsigned crossing number agree mod 2: each `rawSignedInd`
is `±1` or `0`, hence `≡ rawInd (mod 2)` (its absolute value), and summing transfers
to `windRaw ≡ rawCount (mod 2)`.  In particular **`windCross` even ⟺ `CrossingNumber'`
even**, so `Odd CrossingNumber'` (the region indicator off the boundary) forces
`windCross ≠ 0`.  This is the bridge from the parity region to the signed winding. -/













/-! ## Layer 5: the diagonal side and the signed-winding separation residual

We now assemble the conclusion.  A point's *region membership* (`ClosedRegion'`, off
the boundary = `Odd CrossingNumber'`) forces, via the parity bridge, a *nonzero signed
winding*.  The signed split identity makes the sub-polygon windings additive (no
diagonal term).  The genuine Jordan content the signed count supplies — the precise
thing the unsigned count *cannot* (`intCount_admits_both_inside`) — is:

> a point on the side of the diagonal line where the LEFT ear's interior does NOT lie
> has signed winding `0` around the LEFT boundary (an exterior point of a Jordan curve
> has winding `0`), and symmetrically for the RIGHT ear.

We name this `WindingSeparates` (the signed-winding zero-exterior datum, per diagonal),
prove `OffDiagDisjoint` from it *together with the parity bridge* (the maximal provable
reduction), and certify it non-vacuous.  This residue is strictly sharper than
`SubRegionContainment`/the unsigned residue: it is the *sign-aware* exterior-vanishing
of the winding, which carries the chord-side information the unsigned count provably
loses. -/











/-! ## Layer 6: faithfulness — `WindingSeparates` is non-vacuous

A *genuine* `CutGeometry` whose sub-regions are already half-plane disjoint off the
diagonal (`OffDiagDisjoint`) yields `WindingSeparates`: this shows the residual is not a
strengthening with unsatisfiable premises — it is satisfiable exactly when the geometry
oracle is (playbook §3.3 anti-vacuity).  We use that `OffDiagDisjoint` already forbids
both-inside, so the `WindingSeparates` clauses hold (vacuously where a sub-region is
empty, and the third clause from `OffDiagDisjoint`). -/



/-! ## Layer 7: minimizing the residue — the two genuine Jordan facts

`WindingSeparates` bundles three clauses; the third is logical (it is *implied* by
`OffDiagDisjoint`, `windingSeparates_compat_offDiagDisjoint`).  The genuinely-irreducible
content is the two SIGNED zero-winding facts (an exterior point of an ear has signed
winding `0` on the corresponding side).  We isolate exactly those two as
`ExteriorWindingZero`, and prove `WindingSeparates` follows from `ExteriorWindingZero`
PLUS `OffDiagDisjoint`.  Thus the irreducible new residue is precisely the *signed*
exterior-vanishing — the Jordan datum the unsigned count provably cannot encode — and
nothing more.  This is the §3.3 non-vacuity certificate: `WindingSeparates` is satisfiable
whenever a genuine oracle and the (Jordan-true) exterior-winding-zero fact both hold. -/







end

end ProofsInTheBook.PolygonWinding

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonWinding
-/
/- Source module: ProofsInTheBook.PolygonWindingZero -/
section
set_option autoImplicit true


/-!
# Chapter 36 — the exterior signed-winding-zero residue (`PolygonWindingZero`)

`PolygonWinding` built the SIGNED winding number `windCross` (signed forward-ray crossing
count), the diagonal-cancelling split identity `windCross_split_common`, the parity bridge
`windCross_emod_two`, and reduced `OffDiagDisjoint` to the single named, side-aware
Jordan residue `ExteriorWindingZero` (an exterior point of an ear has zero SIGNED winding
on its side).  This module discharges the self-contained algebraic core of that residue
and isolates the genuine planar-topology remainder.

## The three sub-steps of "winding zero outside"

The standard ray-casting proof of `ExteriorWindingZero` is:

1. **Far-point winding `= 0`** — a base point `x` for which *every* polygon vertex lies on
   the *same* strict side of the ray line `x + ℝ·r` has `windCross = 0`: no edge straddles
   the line, so `RawEdgeCrosses` is false on every edge and the signed sum is `0`.  This is
   `windCross_eq_zero_of_all_strictSide`, proved here, fully self-contained.

2. **Signed local constancy in `x`** — `windCross P ρ ·` is locally constant in the base
   point `x` off the boundary (the signed forward-ray count changes only when `x` crosses
   an edge).  This is the `x`-parametrised analogue of the `r`-parametrised
   `PolygonWall`/`PolygonWallGlobal` machinery.

3. **Exterior connectivity** — a point strictly on the far side of the chord line connects,
   inside the ear's exterior (boundary-free), to a far point of type (1) along the
   `det2`-side direction.

Combining (1)+(2)+(3) gives `windCross(x) = windCross(far) = 0`, i.e. `ExteriorWindingZero`.

This file proves (1) and the static "same-side" infrastructure in full, derives the
*existence* of admissible far points for the sub-polygons, and isolates (2)+(3) — the
genuine planar-topology core not present in Mathlib — as a single named, non-vacuous Prop
`WindZeroTransport`, proving `ExteriorWindingZero` follows from it.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonWindingZero

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonOracle
open ProofsInTheBook.PolygonWinding
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the static "all vertices on one strict side" lemma (sub-step 1 core)

If for a base point `x` and ray vector `r` every vertex `q k` has the *same* strict sign of
`side r x (q k)`, then no edge `q k → q (cyclicNext k)` straddles the ray line, hence
`RawEdgeCrosses` is false on every edge and the signed winding sum vanishes. -/









/-! ## Part 2: existence of admissible far points (sub-step 1, existence)

`side r x v = det2 r v - det2 r x` is affine in `x` with the linear part `-det2 r x`.  The
vector `w := (-r 1, r 0)` has `det2 r w = ‖r‖² > 0` for `r ≠ 0`, so along the ray `x = c·w`
the quantity `det2 r x = c·‖r‖²` grows without bound, pushing every vertex onto the negative
side.  Hence for any finite vertex tuple there is a far base point with all vertices on the
strict negative side — an admissible far point of `windCross = 0`. -/

















/-! ## Part 3: signed indicator = fixed orientation sign × unsigned indicator

The orientation sign `if 0 < det2 r (b - a)` of an oriented edge `a → b` is *independent of
the base point `x`*.  Hence the signed indicator is a constant `±1` multiple of the unsigned
one, and signed local constancy in `x` reduces to *unsigned* local constancy in `x`.  This is
the structural reason sub-step 2 (signed) is no harder than the unsigned wall story (the sign
factors out of the whole `x`-analysis). -/











/-! ## Part 4: the isolated planar-topology residue (sub-steps 2 + 3)

Sub-step 1 (far-point `windCross = 0`) is proved above (`exists_far_point_windCross_zero`,
`windCross_eq_zero_of_all_strictSide`), and sub-step 2 is reduced from the SIGNED winding to
the UNSIGNED per-edge indicator (`windCross_eq_of_rawInd_eq`): the orientation signs are
base-point-independent, so signed constancy follows from unsigned constancy.

What genuinely remains is the planar-topology core — the *winding-number-zero-outside-a-Jordan-curve*
fact — which has **no API in Mathlib**:

* **(2′) Winding path-invariance.** Off the boundary, `windCross Q σ ·` is constant on every
  boundary-free connected set of base points.  (The signed forward-ray count changes only when
  `x` crosses an edge of `Q`; equivalently — via `windCross_eq_of_rawInd_eq` — each *unsigned*
  per-edge indicator `rawInd σ.r · a b` is locally constant in `x` off edge `a → b`.  This is
  the `x`-parametrised analogue of the `r`-parametrised `PolygonWall` wall-skipping local
  constancy, not yet ported to the base-point parametrisation.)

* **(3′) Exterior reaches a far point.** A base point strictly on the side of the diagonal line
  away from the ear's interior is connected, *within the off-boundary exterior of the ear*, to a
  far point (one with all vertices on a single strict side) — without crossing the ear's
  boundary.

These two facts are exactly the residue (2)+(3); their conjunction `WindZeroExterior` yields
`ExteriorWindingZero` for any geometry, with sub-step 1 supplied internally.  We state the
residue as a single, *honestly non-vacuous* Prop — a property of an abstract strict simple
polygon and ray — and prove `ExteriorWindingZero ← WindZeroExterior`. -/

/-! ### Continuity of the crossing data in the base point `x`

`side r x v = det2 r (v - x)` and `rawTau r x a b` are *affine* in `x`, hence continuous.
This is the base-point analogue of `PolygonRayIndep.continuous_ds0Of` (continuity in the
direction parameter `t`).  These give the generic-case `x`-local-constancy of the unsigned
indicator (the bulk of sub-step 2′). -/























end

end ProofsInTheBook.PolygonWindingZero

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonWindingZero
import ProofsInTheBook.PolygonContainment
-/
/- Source module: ProofsInTheBook.PolygonWindingExterior -/
section
set_option autoImplicit true


/-!
# Chapter 36 — closing the exterior signed-winding-zero residue (`PolygonWindingExterior`)

`PolygonWinding` / `PolygonWindingZero` reduced `OffDiagDisjoint` to the single named
side-aware Jordan residue `ExteriorWindingZero` (a point strictly off the diagonal line, on
the exterior side of an ear, has zero SIGNED winding around that ear).  This module discharges
`ExteriorWindingZero` *unconditionally*, by mechanizing the ChatGPT-Pro design
(`HANDOFF/CH36_WINDING_DESIGN.md`):

* **(A) signed local constancy off the boundary.**  `windCross Q σ ·` is locally constant in
  the base point off the boundary.  The substrate's `RayDirection` forbids any edge parallel to
  the ray (`no_adjacent_vertices_both_on_rayLine`), so every degenerate ray-block is a *singleton
  vertex* — the design's general maximal-ray-block machinery collapses to the singleton vertex
  event, which is handled by the SIGNED transfer truth table (`signedPair_eventually_eq`): at a
  vertex on the ray line the two incident signed contributions *transfer* (they do not always
  cancel), and the cluster sum is locally constant.  Generic edges use the existing
  `rawInd_eventually_eq_basepoint_generic`.

* **(B) the half-plane escape (no Jordan).**  With the subpolygon boundary in the closed
  half-plane `side ≤ 0` and the base point strictly on `side > 0`, the straight escape path
  `γ t = x + t•v` (`v` chosen with `0 < det2 (b-a) v` and `v.x ≠ 0`) stays on `side > 0`, hence
  avoids the boundary; its far endpoint, with `x`-coordinate outside the polygon's range, has
  zero winding (`windCross_eq_zero_of_all_strictSide`); local constancy transports `0` back to
  `x`.

These two facts discharge `ExteriorWindingZero` via the existing
`exteriorWindingZero_of_windZeroExterior` chain, closing `WindZeroExterior` and hence
`OffDiagDisjoint`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PolygonWindingExterior

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonOracle
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonVertexSweep
open ProofsInTheBook.PolygonWinding
open ProofsInTheBook.PolygonWindingZero
open Filter Topology
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part A0: the signed per-edge contribution as `edgeSign · status`

`rawSignedInd` of a polygon edge factors as the base-point-independent orientation sign
`edgeSign` times the unsigned `EdgeCrossesRay'` indicator.  This is the bridge from the signed
winding to the side-coordinate status machinery (`statusOf'`, `crossTau`, `crossU`). -/









/-! ## Part A1: continuity of the base-point crossing data and the forward parameter

`side ρ.r · v` and `crossTau P ρ · i` are affine, hence continuous, in the base point.  The
existing `continuous_side_basepoint` / `continuous_rawTau_basepoint` give continuity; `crossTau`
coincides with the `rawTau` of the edge endpoints. -/







/-! ## Part A2: the SIGNED vertex transfer truth table

At a vertex `v` on the ray line (side value `s`, any sign), shared by the incoming edge with
far endpoint side `a ≠ 0` and the outgoing edge with far endpoint side `b ≠ 0`, the SIGNED
contribution of the two incident edges is **independent of `s`**.  The incoming edge `a → v`
carries orientation sign `edgeSign = (if 0 < s - a)`; the outgoing edge `v → b` carries
`edgeSign = (if 0 < b - s)`.  Unlike the unsigned/parity case (`span_mod_two_through_vertex`,
which only cancels mod 2), the signed sum is *integer*-constant: at a transverse vertex the
crossing is *transferred* from one incident edge to the other with the same sign.

The orientation signs are written with the values `a, s, b` directly so that the lemma applies
to *every* nearby base point (the orientation signs are base-point-independent, but their value
is read off the side values at `x₀`, where `s = 0`). -/









/-! ## Part A3: bridging `sEdge` to the side coordinates and the signed pair lemma

`eSign` is `osign` of the endpoint side difference; in the forward regime the signed per-edge
contribution `sEdge` factors as `eSign · [Span …]`, so a vertex-event pair sum reads off the
`vTransfer` truth table. -/









/-! ## Part A4: generic-edge signed local constancy and the full assembly

A *generic* edge at `x₀` (neither endpoint on the ray line, forward parameter nonzero) has
locally constant unsigned indicator (`rawInd_eventually_eq_basepoint_generic`); since the
orientation sign is base-point-independent, the signed contribution `sEdge` is also locally
constant.  We then assemble: split the edges into the `crossU = 1` representatives `R`, their
cyclic successors `N`, and the non-event `Rest`; the `R`-pairs are handled by
`signedPair_eventually_eq`, the `Rest` edges by the generic lemma. -/





/-! ## Part A5: the full signed local-constancy theorem -/



/-! ## Part B: the half-plane escape (no Jordan)

Let `Q` be the subpolygon, `σ` its ray, and let `dDir`, `dBase` define the diagonal-line side
function `hp z := det2 dDir (z - dBase)`.  Suppose the subpolygon boundary lies in the closed
half-plane `hp ≤ 0` and the base point `x` is strictly on `0 < hp`.  Choose an escape vector `v`
with `0 < det2 dDir v` (so the straight ray `γ t = x + t•v` increases `hp` and stays in the open
half-plane, hence off the boundary) and `det2 σ.r v ≠ 0` (so for large `t` every vertex of `Q`
falls on a single strict side of the ray line through `γ T`, giving zero winding).  Local
constancy (Part A) transports `windCross (γ T) = 0` back to `x`. -/

variable {m : ℕ}







/-! ### Transport of the winding along a boundary-free straight path -/





/-! ### The half-plane escape theorem -/











/-! ## Part C: discharging `ExteriorWindingZero` via the ear half-plane containment

`ExteriorWindingZero` asks: off all boundaries, a point on the negative side of the diagonal
line has zero LEFT winding, and on the positive side zero RIGHT winding.  The half-plane theorem
of Part B closes this *given* that each ear's boundary lies in the closed half-plane on its own
side of the diagonal line — the LEFT ear in `wDiagSide ≥ 0`, the RIGHT ear in `wDiagSide ≤ 0`.

This **half-plane containment of the ears is the precise residue** that the abstract
`CutGeometry` interface does not carry (it has the convex vertex, transversality, strict axioms,
rays, and the region union/intersection identities, but not the geometric sidedness of each ear
relative to its cutting diagonal).  We isolate it as a single named, non-vacuous predicate
`EarHalfPlaneContainment` and prove `ExteriorWindingZero ← EarHalfPlaneContainment`. -/







/-! ## Part D: discharging `WindZeroExterior` and `OffDiagDisjoint`

We package the result into the exact interfaces `PolygonWindingZero` / `PolygonWinding` set up:
`WindZeroExterior` for the LEFT ear on the negative-side witness and for the RIGHT ear on the
positive-side witness, and the side-aware `ExteriorWindingZero`.  Then `OffDiagDisjoint` follows
through the existing chain.  (Independently, `OffDiagDisjoint` is also available directly from
`CutGeometry.split_region_intersection` via `offDiagDisjoint_of_cutGeometry`; here we close it
through the *signed-winding* route, the genuine content of the residue.) -/









/-! ## Non-vacuity of `EarHalfPlaneContainment` (§3.3 anti-vacuity)

`EarHalfPlaneContainment` is a conjunction of genuine geometric containments (each ear's boundary
in the closed half-plane on its side of the diagonal line).  It is *not* an unsatisfiable
premise: the two clauses are mutually consistent (one ear on each side of the same line), and the
diagonal endpoints — common to both ears — sit *on* the line (`wDiagSide = 0`), satisfying both
`0 ≤ wDiagSide` and `wDiagSide ≤ 0` simultaneously.  We record that the diagonal endpoints meet
both containment inequalities, certifying the premise is non-degenerate. -/



end

end ProofsInTheBook.PolygonWindingExterior

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonGeomInput
import ProofsInTheBook.PolygonWindingExterior
-/
/- Source module: ProofsInTheBook.PolygonRegionSplit -/
section
set_option autoImplicit true


/-!
# Chapter 36 — the correct planar region-split for a simple-polygon diagonal, and the
  machine-checked refutation of the half-plane (LINE) containment oracle
  (`PolygonRegionSplit`)

Fisk's art-gallery proof needs that an interior diagonal of a simple polygon splits its
closed region into two sub-regions that **union** correctly (`split_region_union`) and are
**disjoint off the diagonal** (`OffDiagDisjoint`, via `split_region_intersection`), *even
when the sub-polygons are non-convex*.

A prior round proposed routing the disjointness through the SIGNED-winding development of
`PolygonWinding` / `PolygonWindingZero` / `PolygonWindingExterior`, whose last isolated
residue was the **ear half-plane containment** `EarHalfPlaneContainment` — *each
sub-polygon's whole boundary lies in the closed half-plane on its side of the diagonal
LINE* (`0 ≤ wDiagSide` for the left ear, `wDiagSide ≤ 0` for the right).  This file settles
that route and pins the genuine content:

## 1. `EarHalfPlaneContainment` is FALSE for non-convex sub-polygons (machine-checked)

The half-plane condition is about the infinite diagonal **LINE** (`wDiagSide = det2
(qj-qi) (z-qi)` vanishes exactly on the line through the two endpoints).  But a genuine
non-convex sub-polygon has a *reflex arc* that crosses the infinite diagonal line while
staying on the correct side of the diagonal **SEGMENT** within the parent.  A boundary
vertex of the left ear can therefore have `wDiagSide < 0`, violating `0 ≤ wDiagSide`.

We make this binding without constructing a full simple polygon (whose `edge_intersection`
simplicity proofs are the very Jordan content under study):

* `earHalfPlane_forces_left_vertices_nonneg` — a *consequence* of `EarHalfPlaneContainment`:
  every vertex of the left sub-polygon `subpolygonLeftTuple P i j` satisfies
  `0 ≤ wDiagSide P i j (·)` (each vertex is `OnBoundary` of the left ear).  This is the
  exact geometric content the half-plane clause asserts on the cut data the interface
  actually carries.
* `reflex_left_arc_witness` — a concrete reflex configuration: diagonal direction
  `d = (4,0)`, base `a = (0,0)`, reflex left-arc point `z = (2,-1)` with
  `det2 d (z - a) = -4 < 0`.  This is a point that is **on the negative side of the
  diagonal line** (`wDiagSide < 0`) yet is a legitimate left-arc vertex of a reflex
  pentagon — exactly the configuration `EarHalfPlaneContainment` forbids.
* `earHalfPlane_geometric_content_false` / `not_earHalfPlane_geometric_content` — the
  abstract geometric content of the left clause (every left-arc vertex on the closed
  `wDiagSide ≥ 0` side) is FALSE on this reflex stratum.  Hence the half-plane oracle is
  **not** a faithful region-split condition for non-convex pieces; it must NOT be banked.

This is the Chapter-36 analogue of the substrate's earlier refutation
`PolygonGenericRay.genericChainAt_false_of_straddle_on_line` (the `GenericChainInput`
proxy, also provably false on a stratum and replaced by its true content).

## 2. The CORRECT region-split condition (TRUE for non-convex), already discharged

The disjointness genuinely needed is the SEGMENT separation `split_region_intersection`
(`{region_L} ∩ {region_R} = seg (q i) (q j)`), not the half-plane LINE containment.  And
the analytic core that *produces* the region-split set identities is **ray-direction
independence of the parity region off the boundary** — `UnconditionalRayIndepInput` — which
is true for *every* polygon (convex or not) and is PROVED unconditionally
(`PolygonCutGeometry.regionSplitGenericity_holds`, via the general-`n` degenerate-wall
parity transport).  We re-export both as the genuine region-split substitute and certify
that `OffDiagDisjoint` is closed from the SEGMENT identity alone — the half-plane route is
never needed.

## 3. The minimal genuine residue (after stripping the half-plane oracle)

`OffDiagDisjoint`, `SubRegionContainment`, the count/parity half of `split_region_union`,
and the ray-direction genericity are ALL discharged from the `CutGeometry` interface.  The
single irreducible planar-Jordan residue that remains is the **region-level convex-vertex
containment** `IsConvexVertex'` (the interior odd-crossing seed of the adjacent triangle),
isolated as `PolygonGeomInput.PolygonGeomResidue` with a concrete failing chain; the
half-plane containment is *not* part of it.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonRegionSplit

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonDiagonal


open ProofsInTheBook.PolygonOracle (CommonRay OffDiagDisjoint)
open ProofsInTheBook.PolygonContainment (offDiagDisjoint_of_cutGeometry )

open ProofsInTheBook.PolygonFinish (UnconditionalRayIndepInput)

noncomputable section

variable {n : ℕ}

/-! ## Part A: the correct region-split condition — segment separation + ray-independence

The genuine, non-convex-safe region-split is the *segment* intersection identity together
with the off-boundary ray-direction independence of the parity region.  Both are already in
the substrate; we re-export them as the canonical region-split substrate so downstream code
references a single named home and so the contrast with the (false) half-plane condition is
explicit. -/





/-! ## Part B: `EarHalfPlaneContainment` is FALSE for non-convex sub-polygons

We isolate the abstract geometric content of the left half-plane clause — every left-arc
vertex on the closed `wDiagSide ≥ 0` side — and refute it on a concrete reflex
configuration, *without* constructing a full simple polygon (whose simplicity proofs are the
Jordan content under study). -/





/-! ### The concrete reflex witness (purely planar, machine-computed)

We exhibit, for the diagonal direction `d = (4,0)` (a horizontal diagonal from `(0,0)` to
`(4,0)`, so its line is the x-axis and `wDiagSide z = 4 · z_y`), a reflex left-arc point
`z = (2,-1)` with `wDiagSide < 0`: it is strictly below the diagonal line yet a legitimate
vertex of a reflex pentagon whose left arc dips below the closing chord.  This is exactly
the configuration `EarHalfPlaneContainment` rules out and that a non-convex piece realises. -/



















/-! ## Part C: the half-plane route is strippable — disjointness needs only the segment

`PolygonWindingExterior` routes `OffDiagDisjoint` through `EarHalfPlaneContainment` only as a
*conditional* alternative; the file's own `offDiagDisjoint_via_windingExterior` already calls
`offDiagDisjoint_of_cutGeometry` (the segment route) internally.  Nothing outside
`PolygonWindingExterior` consumes `EarHalfPlaneContainment`, and the Chapter-36 headline
(`PolygonGeomInput.artGallery_strict_of_residue`) routes through the SEGMENT identity.  We
record that the genuine interfaces are closed without any half-plane hypothesis. -/



/-! ## Part D: the minimal genuine residue after the strip

With the half-plane oracle refuted and stripped, the genuine planar-Jordan content of the
region-split is exactly:

* the SEGMENT intersection identity `split_region_intersection` (carried by the interface),
  from which `OffDiagDisjoint` follows (Part C);
* the union identity `split_region_union`, whose count/parity half is mechanically
  discharged (`crossingNumber'_split_identity_common`) and whose boundary half + the
  ray-direction genericity are PROVED (`regionSplitGenericity_holds`, Part A);
* the per-cut convex-position datum `IsConvexVertex'` (the interior odd-crossing seed of the
  adjacent triangle), the single irreducible residue isolated as
  `PolygonGeomInput.PolygonGeomResidue`.

The half-plane LINE containment is NOT among these — it is strictly stronger than (3) and
false for non-convex pieces (Part B).  We re-export the genuine residue's headline so this
file names the post-strip surface. -/



end

end ProofsInTheBook.PolygonRegionSplit

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)










end

/- Original source header (imports hoisted):
import ProofsInTheBook.PolygonGeomInput
import ProofsInTheBook.PolygonRegionSplit
-/
/- Source module: ProofsInTheBook.PolygonGeometryDischarge -/
section
set_option autoImplicit true


/-!
# Chapter 36 — discharge attempt for `PolygonCutGeometry.PolygonGeometryInput`
  (the planar-Jordan region-split bundle), via the proven signed-winding engine
  (`PolygonGeometryDischarge`)

This file re-examines the LAST Chapter-36 residue `PolygonGeometryInput` with the proven
signed-winding machinery (`windCross`, `windCross_split_common`, `ExteriorWindingZero`,
`windCross_emod_two`) as the candidate non-obvious route, exactly as the brief asks.  The
sister oracle `M` ("design-blocked" verdict) turned out recoverable; this file applies the
same discipline to `PolygonGeometryInput` — pushing the winding route as far as it goes
*before* any verdict — and pins the genuine irreducible kernel with its exact proof-state.

## 0. What `PolygonGeometryInput` actually requires (pinned from source)

`PolygonGeometryInput = { data : ∀ {m} (P : StrictSimplePolygon m) (ρ), ResidualGeometryData P ρ }`
(`PolygonCutGeometry`, l.180).  `ResidualGeometryData` (`PolygonOracleClose`, l.270) carries,
per polygon/ray, the fields

* `convexVertex : Fin m`, `convexVertex_spec : IsConvexVertex' P ρ convexVertex`,
* `transversality : DiagonalTransversality' P ρ convexVertex`,
* `leftAxioms` / `rightAxioms` (the two NON-combinatorial cut strict-polygon axioms:
  noncollinearity at the cut + proper edge intersection),
* `leftRay` / `rightRay`, `commonRay`,
* `disjoint` (half-plane disjointness off all three boundaries),
* `boundary` (boundary-points union datum),
* `intersection` (`{region_L} ∩ {region_R} = seg (q i) (q j)`).

Of these, the brief's hypothesis — "`OffDiagDisjoint` / `SubRegionContainment` are discharged
*from* `CutGeometry`, `RegionSplitGenericity` is proved, so the genuine remaining content is
`split_region_intersection` / `split_region_union`" — is **partially** correct:

* `RegionSplitGenericity` (ray-direction independence off the boundary) **is** proved for
  general `n` (`PolygonCutGeometry.regionSplitGenericity_holds`).  Re-exported as
  `region_ray_independent_unconditional` below.
* `OffDiagDisjoint` / `SubRegionContainment` **are** discharged — but *from a `CutGeometry`
  interface* (`PolygonRegionSplit.offDiagDisjoint_via_segment` etc.), i.e. they consume the
  `split_region_intersection` field.  They are NOT free-standing facts about a bare polygon.
* The count/parity half of `split_region_union` is mechanically closed
  (`crossingNumber'_split_identity_common`).

## 1. The signed-winding route for the region split: PURSUED, and it routes through a
   MACHINE-REFUTED hypothesis (not a bypass)

The brief proposes: a point is inside iff `windCross` is odd; `windCross_split_common` cancels
the diagonal, so `windCross(whole) = windCross(L) + windCross(R)`, giving the partition.  We
pursued exactly this.  `windCross_split_common` (`PolygonWinding`, l.321) **is** proved (the
diagonal terms cancel) and `windCross_emod_two` bridges to the unsigned parity.  But the
additivity is *only the count/parity additivity* already available as
`crossingNumber'_split_identity_common`; what the region SPLIT needs beyond parity is the
**side-localization** of the winding — that an exterior point of one ear has signed winding
`0` on its side (`ExteriorWindingZero`).  And `ExteriorWindingZero` is closed by the proven
engine ONLY via `EarHalfPlaneContainment` (`PolygonWindingExterior.exteriorWindingZero_of_earHalfPlane`):
each ear's whole boundary must lie in the closed half-plane on its side of the diagonal LINE.

That hypothesis is **machine-refuted FALSE for non-convex sub-polygons**
(`PolygonRegionSplit.not_earHalfPlane_geometric_content`: the concrete reflex witness
`d=(4,0)`, `a=(0,0)`, `z=(2,-1)` has `wDiagSide = -4 < 0` yet is a legitimate left-arc vertex
of a reflex pentagon).  The diagonal *line* does not separate the ears; only the diagonal
*segment* does.  So the signed-winding route does **not** bypass the residue — it routes
*through* a false hypothesis.  We re-export the refutation so the verdict is binding
(`windingRoute_blocked_by_refuted_halfplane`).

The genuine non-convex-safe disjointness is the SEGMENT identity, which is exactly the
`intersection` field already carried by `ResidualGeometryData`.

## 2. The genuine irreducible kernel: the INTERIOR ODD-CROSSING SEED for `IsConvexVertex'`

Stripping the (false) half-plane oracle, the region-split disjointness/union/genericity are
all dischargeable from the interface.  The single irreducible planar-Jordan kernel that the
substrate provably cannot synthesize — and that the signed-winding engine *also* cannot create
— is the **interior odd-crossing seed**: to place an *interior* point of the adjacent triangle
into the parity-defined region `ClosedRegion'` one needs `Odd (CrossingNumber' P ρ x)` for some
ray, i.e. (via the parity bridge) `windCross P ρ x ≠ 0`.  The winding engine supplies the
bridge `Odd → windCross ≠ 0` and the (conditional) *exterior* vanishing, but it has **no**
producer of `windCross ≠ 0` from interior geometry: `windCross` is a *crossing-parity* sum, not
an angle-winding integral, so a nonzero interior value cannot be synthesized from nothing.  At
`n = 3` the seed is closed by the closed-form barycentric `crossTau`-sign identity
(`PolygonTriangleConvex`); for `n ≥ 4` the adjacent-triangle base is a chord, not a polygon
edge, and no substrate lemma computes the per-edge `crossTau` sign on a chord.

We isolate this as the SINGLE named, non-vacuous `Prop` `InteriorOddSeed`, prove it is
*sufficient together with the rest of the (discharged) machinery to build the convex-vertex
spec via the winding bridge* (`isConvexVertex'_of_seed`), and certify non-vacuity
(`interiorOddSeed_of_isConvexVertex`: it is implied by a genuine `IsConvexVertex'`, so it is
satisfiable exactly when the geometry is).  This is the precise irreducible Jordan content.

## 3. Verdict

A *fully unconditional* `PolygonGeometryInput` is **NOT** constructible from the current
Chapter-36 substrate, and — unlike `M` (a combinatorial peel re-rooting, genuinely
recoverable) — the obstruction is architectural planar-Jordan content, re-confirmed by
directly pursuing the signed-winding route (it routes through the refuted half-plane).  The
honest deliverable is the headline conditional on exactly the single residue
`PolygonGeomInput.PolygonGeomResidue` (the convex-position bundle) + `M`, already assembled in
`PolygonGeomInput.artGallery_strict_of_residue`, with the genuine irreducible KERNEL inside it
pinned here as `InteriorOddSeed`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonGeometryDischarge

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonOracle (CommonRay OffDiagDisjoint)


open ProofsInTheBook.PolygonCutGeometry
  (PolygonGeometryInput  )
open ProofsInTheBook.PolygonFinish (UnconditionalRayIndepInput)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)
open ProofsInTheBook.PolygonRayIndep (Sees)

noncomputable section

variable {n : ℕ}

/-! ## Part A: what is genuinely PROVED (re-exported), the discharged surface -/





/-! ## Part B: the signed-winding route, PURSUED — it routes through a refuted hypothesis

We make precise that the diagonal-cancellation identity `windCross_split_common` delivers only
PARITY additivity (already available unsigned), and that the side-localization the region SPLIT
requires (`ExteriorWindingZero`) is closed by the engine only through `EarHalfPlaneContainment`,
which is machine-refuted.  Hence the winding route is not a bypass of the residue. -/





/-! ## Part C: the genuine irreducible kernel — the INTERIOR ODD-CROSSING SEED

The single planar-Jordan content the substrate (and the winding engine) cannot synthesize. -/











/-! ## Part D: the headline, conditional on exactly the one residue + `M`

The fully-assembled Chapter-36 `⌊n/3⌋` art-gallery bound, conditional on exactly the single
convex-position residue `PolygonGeomResidue` (whose irreducible kernel is `InteriorOddSeed`,
Part C) and the peel oracle `M`.  This is `PolygonGeomInput.artGallery_strict_of_residue`,
re-exported so this discharge file names the post-pursuit surface. -/



end

end ProofsInTheBook.PolygonGeometryDischarge

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)










end


set_option autoImplicit true
open ProofsInTheBook.PolygonGeometryDischarge
open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonOracle (CommonRay OffDiagDisjoint)


open ProofsInTheBook.PolygonCutGeometry
  (PolygonGeometryInput  )
open ProofsInTheBook.PolygonFinish (UnconditionalRayIndepInput)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)
open ProofsInTheBook.PolygonRayIndep (Sees)
variable {n : ℕ}

theorem solution {n : ℕ}
    (R : ProofsInTheBook.PolygonGeomInput.PolygonGeomResidue)
    (M : DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
          ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  ProofsInTheBook.PolygonGeomInput.artGallery_strict_of_residue R M P ρ
