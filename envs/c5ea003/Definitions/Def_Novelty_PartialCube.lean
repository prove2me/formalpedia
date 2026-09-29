-- Prove2me | Definitions.Def_Novelty_PartialCube
-- name    : Novelty_PartialCube
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:31:45.491897+00:00
-- url     : https://prove2.me/theorems/6ed9dbf0-7cf9-47c7-a961-ca719b7061af
-- title:
--   Aether Catalog definitions — Novelty_PartialCube
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.PartialCube`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/PartialCube.lean by skeleton subtraction
import Mathlib

/-!
# Daisy cubes are partial cubes

A *daisy cube* is, by the theorem of Klavžar and Mollard, an isometric subgraph of a hypercube,
i.e. a *partial cube*.  Here we model the vertices of the hypercube `Q_n` as elements of
`Finset (Fin n)` (a vertex is the set of coordinates equal to `1`), the Hamming distance as the
cardinality of the symmetric difference, and a daisy cube as the subgraph induced by a
*down-closed* vertex set.  We prove the foundational structural fact underlying the whole theory of
forbidden pc-minors for daisy cubes: **a daisy cube is an isometric subgraph of the hypercube**
(it is a partial cube).

The proof has two halves:
* `walk_length_ge` — in any subgraph of `Q_n`, a walk needs at least `hdist` edges (a lower bound
  that holds for *every* vertex set, by the triangle inequality);
* `daisy_geodesic` — in a daisy cube there is a walk of exactly `hdist` edges that never leaves the
  daisy cube, obtained by first descending to the meet `A ∩ B` and then ascending to `B`.

Together they give `daisy_isometric`.

References (catalog): Djokovic1973, Winkler1984 (Θ-classes of partial cubes); the daisy-cube
specialization is due to Klavžar–Mollard.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The class of daisy cubes (down-closed vertex sets of `Q_n`) is contained
in the class of partial cubes (isometric subgraphs of `Q_n`).  This is the geometric precondition
making "forbidden pc-minor" characterizations meaningful: every member of the class must itself be a
partial cube.

Experiment (Experimenter): Encode vertices as `Finset (Fin n)`, distance as symmetric-difference
cardinality.  Lower bound on any walk via the symmetric-difference triangle inequality
(`symmDiff_triangle`).  Upper bound via an explicit meet-join geodesic, built by strong induction on
`hdist A B`: while `A ≠ B`, either delete a coordinate of `A \ B` (stays `⊆ A`, hence in `D`) or
insert a coordinate of `B \ A` (stays `⊆ B`, hence in `D`), strictly decreasing the distance.

Analysis (Analyst): The lower bound is independent of down-closure — it is a pure hypercube fact.
Down-closure is used *only* to keep the constructed geodesic inside the vertex set; this isolates
exactly where the daisy-cube hypothesis is needed.

Critique (Critic): The result is not vacuous — `IsLeast` packages both an existence (geodesic in `D`)
and a genuine minimality (no shorter walk exists), and the proof uses induction, `rcases`, and the
triangle inequality rather than `decide`/`simp` alone.

Synthesis (PI): `daisy_isometric` is the structural anchor of the forbidden-minor program; see
`FUTURE_DIRECTIONS.md`.
-/

open scoped symmDiff
open Finset

namespace DaisyCube

variable {n : ℕ}

/-- Hamming distance between two vertices of `Q_n`. -/
def hdist (A B : Finset (Fin n)) : ℕ := (A ∆ B).card

/-- Adjacency in `Q_n`: Hamming distance `1`. -/
def Adj (A B : Finset (Fin n)) : Prop := hdist A B = 1

/-- A *daisy cube* is the subgraph of `Q_n` induced by a down-closed vertex set. -/
def IsDaisy (D : Finset (Fin n) → Prop) : Prop := ∀ ⦃A B⦄, D A → B ⊆ A → D B

/-- `IsWalk A l`: `l` lists the successive vertices visited after the start vertex `A`, each
adjacent to the previous one. The number of edges is `l.length`. -/
def IsWalk : Finset (Fin n) → List (Finset (Fin n)) → Prop
  | _, [] => True
  | A, B :: l => Adj A B ∧ IsWalk B l





/-
Deleting a coordinate present in `A` is an adjacency move.
-/

/-
Inserting a coordinate absent from `A` is an adjacency move.
-/

/-
Deleting a coordinate of `A \ B` decreases the distance to `B` by one.
-/

/-
Inserting a coordinate of `B \ A` decreases the distance to `B` by one.
-/

/-
**Lower bound.** Every walk from `A` to its last vertex uses at least `hdist` edges. This holds
in *every* subgraph of `Q_n`; it does not require down-closure.
-/

/-
**Geodesic existence.** In a daisy cube, any two vertices are joined by a walk with exactly
`hdist` edges that never leaves the daisy cube.
-/


end DaisyCube


