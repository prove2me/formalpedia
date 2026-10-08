-- Prove2me | Definitions.Def_P2MAssembly_Chapter12
-- name    : P2MAssembly_Chapter12
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T16:16:59.279063+00:00
-- url     : https://prove2.me/theorems/61a72ff8-069d-4d76-b395-c8e97a1702a6
-- title:
--   Dart permutations, orbit counts, and regular sphere maps
-- statement:
--   Let D be a finite set of darts (with decidable equality in the formalization). A combinatorial map M consists of permutations $\alpha,\sigma$ of D, with $\alpha^2=1$ and $\alpha(d)\ne d$ for all darts. Put $\varphi=\sigma\circ\alpha$; the numbers V,E,F count the orbits of $\sigma,\alpha,\varphi$, respectively. The Euler characteristic is the integer $V-E+F$. A dart step either remains within a vertex orbit or crosses the edge pairing. Connectedness means that every pair of darts is related by a finite sequence of these steps, including the empty sequence. The predicate IsSphereMap is defined by connectedness together with $V-E+F=2$.
--
--   FaceRegular(p) requires every face orbit to have p darts; VertexRegular(q) requires every vertex orbit to have q darts. These are combinatorial definitions. They do not include the degree-pair inequality, its five-pair conclusion, an embedding construction, or existence of a geometric polyhedron.
-- source:
--   Original map definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMap.lean#L24. Chapter use: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter12.lean#L50. Topic: Proofs from THE BOOK, 6th edition, Chapter 13, “Three applications of Euler’s formula” (https://doi.org/10.1007/978-3-662-57265-8_13).

import Init
import Mathlib

/- Source module: ProofsInTheBook.PlanarMap -/
section


/-!
# Planar maps via combinatorial maps (Layer 1)

Infrastructure for the faithful formalization of Chapter 12 (Euler's formula applications)
and Chapter 35 (Five Color Theorem), which Mathlib currently lacks.

A **combinatorial map** is a finite dart set `D` with an edge involution `α` (fixed-point-free)
and a vertex rotation `σ`. Vertices = `σ`-orbits, edges = `α`-orbits, faces = `φ`-orbits where
`φ = σ * α`. The Euler characteristic `V - E + F` equals `2 - 2g` for genus `g`; a **plane**
(sphere) map is the faithful genus-zero notion `IsSphereMap := Connected ∧ eulerChar = 2`
(NOT an inductive build certificate — that would risk an incomplete fragment).

This file is Layer 1: the raw map, the orbit counts, and the Euler characteristic.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

/-- A combinatorial (orientable) map on a finite dart set `D`:
edge involution `α` (fixed-point-free) and vertex rotation `σ`. -/
structure CombMap (D : Type*) [Fintype D] [DecidableEq D] where
  /-- Edge involution: pairs each dart with its reverse. -/
  α : Equiv.Perm D
  /-- Vertex rotation: cyclic order of darts around each vertex. -/
  σ : Equiv.Perm D
  /-- `α` is an involution. -/
  α_invol : α * α = 1
  /-- `α` has no fixed dart (every edge has two distinct darts). -/
  α_no_fixed : ∀ d, α d ≠ d

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Face permutation `φ = σ ∘ α`. Its orbits are the faces. -/
def φ (M : CombMap D) : Equiv.Perm D := M.σ * M.α

/-- The `SameCycle` equivalence of a permutation, as a `Setoid` on the dart set.
Its classes are the orbits (cycles, including fixed points). -/
def cycleSetoid (p : Equiv.Perm D) : Setoid D where
  r := p.SameCycle
  iseqv := ⟨fun x => Equiv.Perm.SameCycle.refl p x, fun h => h.symm, fun h h' => h.trans h'⟩

instance (p : Equiv.Perm D) : DecidableRel (cycleSetoid p).r :=
  (inferInstance : DecidableRel p.SameCycle)

instance (p : Equiv.Perm D) : Fintype (Quotient (cycleSetoid p)) :=
  Quotient.fintype (cycleSetoid p)

/-- Number of vertices: the number of `σ`-orbits. -/
def V (M : CombMap D) : ℕ := Fintype.card (Quotient (cycleSetoid M.σ))

/-- Number of edges: the number of `α`-orbits. -/
def E (M : CombMap D) : ℕ := Fintype.card (Quotient (cycleSetoid M.α))

/-- Number of faces: the number of `φ`-orbits. -/
def F (M : CombMap D) : ℕ := Fintype.card (Quotient (cycleSetoid M.φ))

/-- The Euler characteristic `V - E + F`. -/
def eulerChar (M : CombMap D) : ℤ := (V M : ℤ) - (E M : ℤ) + (F M : ℤ)

/-- Adjacency of the underlying multigraph on darts: same vertex, or joined by an edge. -/
def dartStep (M : CombMap D) (a b : D) : Prop :=
  M.σ.SameCycle a b ∨ b = M.α a

/-- The map is connected if every two darts are linked by a chain of `dartStep`s. -/
def Connected (M : CombMap D) : Prop :=
  ∀ a b : D, Relation.ReflTransGen M.dartStep a b

/-- A **plane (sphere) map**: connected and of Euler characteristic `2` (genus zero).
The faithful combinatorial definition of a planar graph embedding; NOT an inductive build
certificate, so theorems proved for `IsSphereMap` are about all plane graphs. -/
def IsSphereMap (M : CombMap D) : Prop :=
  M.Connected ∧ M.eulerChar = 2











/-- A `p`-regular face structure: every face (`φ`-orbit) has exactly `p` darts. -/
def FaceRegular (M : CombMap D) (p : ℕ) : Prop :=
  ∀ Q : Quotient (cycleSetoid M.φ),
    (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.φ) x = Q)).card = p

/-- A `q`-regular vertex structure: every vertex (`σ`-orbit) has exactly `q` darts. -/
def VertexRegular (M : CombMap D) (q : ℕ) : Prop :=
  ∀ Q : Quotient (cycleSetoid M.σ),
    (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.σ) x = Q)).card = q









end CombMap

end ProofsInTheBook.PlanarMap

end

/- Source module: ProofsInTheBook.Chapter12 -/
section


/-!
# Chapter 12: Three applications of Euler's formula

From "Proofs from THE BOOK":

**Euler's formula**: For any connected planar graph, V - E + F = 2.

Three applications:
1. **Every planar graph is 5-colorable** (or even 4-colorable, but the
   book proves 6-colorable easily, then refines to 5).
2. **The number of edges**: E ≤ 3V - 6 for simple planar graphs.
3. **Regular polyhedra**: There are exactly five Platonic solids.

The proof of Euler's formula proceeds by induction on edges:
removing an edge either merges two faces (keeping V-E+F constant)
or disconnects the graph (handled by the base case of a tree).
-/

namespace ProofsInTheBook.Chapter12

/-!
### Euler's formula and Platonic solids

The classic V - E + F = 2 and its consequence that there are
exactly 5 regular polyhedra (tetrahedron, cube, octahedron,
dodecahedron, icosahedron).

For a regular polyhedron with p-gonal faces and q faces meeting
at each vertex: 1/p + 1/q > 1/2, which has exactly 5 solutions
(3,3), (3,4), (4,3), (3,5), (5,3).
-/





end ProofsInTheBook.Chapter12

end


