-- Prove2me | Definitions.Def_Geometry_ConvexPlaneGraphs
-- name    : Geometry_ConvexPlaneGraphs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:55:08.283346+00:00
-- url     : https://prove2.me/theorems/feb4368b-d3b9-4d58-b8d8-33e5dd433251
-- title:
--   Aether Catalog definitions — Geometry_ConvexPlaneGraphs
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.ConvexPlaneGraphs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/ConvexPlaneGraphs.lean by skeleton subtraction
import Mathlib
/-
# Convex Position and Plane Graphs

This file develops a self-contained combinatorial model of **plane graphs on
points in convex position** and proves exponential lower bounds on their number,
together with the arithmetic mechanism that explains why convex position should
*minimize* the number of plane graphs among all n-point configurations in general
position.

## Background

For a set `P` of `n` points in convex position (labeled `0, …, n-1` around the
hull), a *plane graph* is a straight-line graph on `P` whose edges pairwise do not
cross. Since convex position fixes the cyclic order of the points, two chords
`{a,b}` and `{c,d}` cross iff their endpoints strictly interleave, `a < c < b < d`
(or symmetrically). Thus the number of plane graphs on `n` convex points is a
purely combinatorial quantity, `numPlane n`.

This quantity is OEIS **A054726** (`1, 1, 2, 8, 48, 352, …`), which grows like
`≈ 11.6^n`. The guiding conjecture (the topic of this mission) is that convex
position gives the *fewest* plane graphs among all n-point sets in general
position.

## Main results

* `numPlane_ge_of_plane` : from any plane graph `F`, the number of plane graphs is
  at least `2 ^ |F|` (every subset of a plane graph is plane).
* `numPlane_ge_star`     : `2 ^ (n-1) ≤ numPlane n` (star from vertex `0`).
* `numPlane_ge_fan`      : `2 ^ (2n-3) ≤ numPlane n` for `n ≥ 2` (fan triangulation).
* `convex_minimizes_triLB` / `convex_strict` : the triangulation-subset lower
  bound `2^(3n-3-h)` (for a point set with `h` hull points) is minimized exactly
  at `h = n`, i.e. convex position — the arithmetic core of the conjecture.
* `numPlane_ge_convex_triLB` : the convex triangulation bound `triLB n n` is a
  genuine lower bound for `numPlane n`.

## Lab Notes

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): Convex position minimizes the number of plane graphs.
A weaker, provable shadow: the number of plane graphs on convex points grows at
least exponentially, and the natural triangulation-based lower bound is smallest
for convex position.

Experiment (Experimenter): We built the chord model, verified `numPlane` against
OEIS A054726 (`numPlane 3 = 8`, `numPlane 4 = 48`, `numPlane 5 = 352`), and proved
exponential lower bounds via fixed plane subgraphs (star, fan). We proved the
monotonicity of the triangulation-subset bound `2^(3n-3-h)` in the hull size `h`.

Analysis (Analyst): The full conjecture is open and out of reach; but the "subsets
of a triangulation are plane" idea gives `numPlane ≥ 2^(edges)`, and Euler's
formula makes the edge count `3n-3-h` decrease with hull size `h`, uniquely
minimized at convex position `h=n`. This is *true and clean* and captures the
mechanism, though the true count (≈11.6^n) far exceeds the `2^(2n-3)≈2.83^n`
bound. Distinguish: (a) the exact minimization is HARD/open; (b) the bound
monotonicity is TRUE and formalized here.

Critique (Critic): Are the theorems vacuous? No — `numPlane` is validated against
A054726 numerically, the lower bounds are strict inequalities proved by explicit
constructions, and the monotonicity is a strict inequality for `h < n`. The fan
bound is tight at `n = 3` (`2^3 = 8 = numPlane 3`), ruling out a definitional
artifact. Corner cases: Nat truncated subtraction is handled by `omega`; `n = 0,1`
are consistent (`numPlane 0 = numPlane 1 = 1`).

Synthesis (PI): We deliver a faithful model, numeric validation against OEIS, two
exponential lower bounds, and the convex-minimizes-the-bound theorem, tying the
combinatorial count to the conjecture's mechanism.
-/

namespace ConvexPlaneGraphs

open Finset

/-- A chord of the convex `n`-gon: an ordered pair of distinct vertices `i < j`
(the endpoints of a straight-line edge). -/
abbrev Chord (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- Two chords **cross** iff their endpoints strictly interleave around the convex
hull: `a < c < b < d` (or the symmetric arrangement). This is exactly the
straight-line crossing condition for points in convex position. -/
def cross {n : ℕ} (x y : Chord n) : Prop :=
  (((x.1.1 : ℕ) < y.1.1) ∧ ((y.1.1 : ℕ) < x.1.2) ∧ ((x.1.2 : ℕ) < y.1.2)) ∨
  (((y.1.1 : ℕ) < x.1.1) ∧ ((x.1.1 : ℕ) < y.1.2) ∧ ((y.1.2 : ℕ) < x.1.2))

instance instDecidableCross {n : ℕ} (x y : Chord n) : Decidable (cross x y) := by
  unfold cross; infer_instance

/-- A **plane graph**: a set of chords that pairwise do not cross. -/
def Plane {n : ℕ} (G : Finset (Chord n)) : Prop := ∀ x ∈ G, ∀ y ∈ G, ¬ cross x y

instance instDecidablePlane {n : ℕ} (G : Finset (Chord n)) : Decidable (Plane G) := by
  unfold Plane; infer_instance

/-- The number of labeled plane graphs on `n` points in convex position. -/
def numPlane (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun G : Finset (Chord n) => Plane G)).card




/-! ### The star from vertex 0 -/

/-- The **star** at vertex `0`: all chords with lower endpoint `0`. -/
def starFan (n : ℕ) : Finset (Chord n) :=
  Finset.univ.filter (fun c : Chord n => (c.1.1 : ℕ) = 0)


/-
The star at vertex `0` has `n - 1` chords.
-/


/-! ### The fan triangulation -/

/-- The **fan** triangulation from vertex `0`: all chords touching `0` together
with all boundary edges `{k, k+1}`. -/
def fan (n : ℕ) : Finset (Chord n) :=
  Finset.univ.filter
    (fun c : Chord n => (c.1.1 : ℕ) = 0 ∨ (c.1.2 : ℕ) = (c.1.1 : ℕ) + 1)


/-
The fan triangulation of the convex `n`-gon has `2n - 3` edges.
-/


/-! ### Convex position minimizes the triangulation-subset lower bound

A triangulation of a set of `n` points with `h` of them on the convex hull has
`3n - 3 - h` edges (Euler's formula). Every subset of its edge set is a plane
graph, so any such point set has at least `2^(3n-3-h)` plane graphs. This lower
bound is *decreasing* in the hull size `h`, hence minimized exactly at `h = n`,
i.e. at convex position — the arithmetic mechanism behind the conjecture. -/

/-- The triangulation-subset lower bound for an `n`-point set with `h` hull points. -/
def triLB (n h : ℕ) : ℕ := 2 ^ (3 * n - 3 - h)





/-! ### Parity of the plane-graph count

The boundary chord `{0,1}` joins two consecutive hull vertices, so no chord can
interleave its endpoints: it crosses nothing. Toggling it is therefore a
fixed-point-free involution on the set of plane graphs, forcing `numPlane n` to be
**even** for `n ≥ 2`.

-- !-- Lab Notes -- !--
Hypothesis: the counts `8, 48, 352` are all even — is `numPlane n` always even for
`n ≥ 2`? Experiment: toggling the universally non-crossing boundary edge `{0,1}`
is a fixed-point-free involution on plane graphs. Analysis: parity is robust in
`n` and reflects that every hull edge is crossing-free, an independent binary
degree of freedom consistent with the `2^(2n-3)` bound. Critique: not vacuous —
`numPlane 1 = 1` is odd, so `n ≥ 2` is necessary; the proof is a genuine involution,
not `decide`. Synthesis: a clean `2`-divisibility invariant of the convex count.
-/

/-- The boundary chord `{0,1}` of the convex `n`-gon (needs `n ≥ 2`). -/
def edge01 (n : ℕ) (hn : 2 ≤ n) : Chord n :=
  ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩




/-
**Parity theorem.** For `n ≥ 2`, the number of plane graphs on `n` points in
convex position is even.
-/


end ConvexPlaneGraphs


