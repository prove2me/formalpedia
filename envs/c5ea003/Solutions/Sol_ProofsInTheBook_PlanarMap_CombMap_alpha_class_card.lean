-- Prove2me | solution 1 for ProofsInTheBook.PlanarMap.CombMap.alpha_class_card
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:26:18.742849+00:00
-- url     : https://prove2.me/submissions/3d44b130-5102-4e9f-833b-b62dd948b1f6

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter12


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



namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]























/-- A power of an involution is either the identity or the involution itself. -/
lemma zpow_involution (α : Equiv.Perm D) (h : α * α = 1) (i : ℤ) :
    α ^ i = 1 ∨ α ^ i = α := by
  have hsq : α ^ (2 : ℤ) = 1 := by
    have h2 : α ^ (2 : ℤ) = α * α := by
      rw [show (2 : ℤ) = 1 + 1 from rfl, zpow_add, zpow_one]
    rw [h2, h]
  rcases Int.even_or_odd i with ⟨r, hr⟩ | ⟨k, hk⟩
  · left
    rw [show i = 2 * r by omega, zpow_mul, hsq, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]

/-- The edge containing a dart `d` is exactly `{d, α d}`: the `α`-orbit of any dart has
the two darts of its edge and no more. -/
lemma alpha_sameCycle_iff (M : CombMap D) (d x : D) :
    M.α.SameCycle d x ↔ x = d ∨ x = M.α d := by
  constructor
  · rintro ⟨i, rfl⟩
    rcases zpow_involution M.α M.α_invol i with h1 | h1
    · left; rw [h1]; rfl
    · right; rw [h1]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩



















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


open ProofsInTheBook.PlanarMap
open Equiv
open ProofsInTheBook.PlanarMap.CombMap
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma solution (M : CombMap D)
    (q : Quotient (cycleSetoid M.α)) :
    (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.α) x = q)).card = 2 := by
  obtain ⟨d, rfl⟩ := q.exists_rep
  have hset :
      (Finset.univ.filter
          (fun x => Quotient.mk (cycleSetoid M.α) x = Quotient.mk (cycleSetoid M.α) d))
        = {d, M.α d} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Quotient.eq]
    show M.α.SameCycle x d ↔ x = d ∨ x = M.α d
    constructor
    · intro h; exact (alpha_sameCycle_iff M d x).mp h.symm
    · intro h; exact ((alpha_sameCycle_iff M d x).mpr h).symm
  rw [hset, Finset.card_insert_of_notMem (by
    simp only [Finset.mem_singleton]
    exact fun hcontra => M.α_no_fixed d hcontra.symm), Finset.card_singleton]
