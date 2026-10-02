-- Prove2me | solution 1 for ProofsInTheBook.Chapter12.chapter12
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:26:16.963016+00:00
-- url     : https://prove2.me/submissions/e057f085-ae32-4f08-af58-a29c9c80edee

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

/-- Every `α`-class (edge) has exactly two darts. -/
lemma alpha_class_card (M : CombMap D)
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

/-- Every edge has exactly two darts: `2 * E = |D|`. -/
lemma two_mul_E_eq_card (M : CombMap D) : 2 * M.E = Fintype.card D := by
  have hsum : Fintype.card D
      = ∑ q : Quotient (cycleSetoid M.α),
          (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.α) x = q)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
  rw [hsum, Finset.sum_congr rfl (fun q _ => alpha_class_card M q),
      Finset.sum_const, Finset.card_univ, smul_eq_mul, E, Nat.mul_comm]

/-- Orbit sizes of any permutation sum to the dart count. -/
lemma sum_class_card (p : Equiv.Perm D) :
    ∑ Q : Quotient (cycleSetoid p),
        (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid p) x = Q)).card
      = Fintype.card D := by
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)).symm





/-- Face-counting: `p`-regular faces give `p * F = 2 * E`. -/
lemma faceRegular_pF (M : CombMap D) {p : ℕ} (h : M.FaceRegular p) :
    p * M.F = 2 * M.E := by
  have hs := sum_class_card M.φ
  rw [Finset.sum_congr rfl (fun Q _ => h Q), Finset.sum_const, Finset.card_univ,
    smul_eq_mul] at hs
  rw [two_mul_E_eq_card, F, Nat.mul_comm]; exact hs

/-- Vertex-counting: `q`-regular vertices give `q * V = 2 * E`. -/
lemma vertexRegular_qV (M : CombMap D) {q : ℕ} (h : M.VertexRegular q) :
    q * M.V = 2 * M.E := by
  have hs := sum_class_card M.σ
  rw [Finset.sum_congr rfl (fun Q _ => h Q), Finset.sum_const, Finset.card_univ,
    smul_eq_mul] at hs
  rw [two_mul_E_eq_card, V, Nat.mul_comm]; exact hs

/-- **The Platonic constraint, derived from Euler's formula.**
A regular sphere map with face length `p`, vertex degree `q` (both positive, at least one
edge) satisfies `p * q < 2 * p + 2 * q`, i.e. `1/p + 1/q > 1/2` — the inequality that
bounds the regular convex polytopes to finitely many `(p, q)`. This is the genuine content
of Chapter 12: the constraint is *derived from* Euler `V - E + F = 2`, not assumed. -/
theorem platonic_constraint (M : CombMap D) (hsphere : M.IsSphereMap)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hE : 0 < M.E)
    (hF : M.FaceRegular p) (hV : M.VertexRegular q) :
    p * q < 2 * p + 2 * q := by
  have hpf : (p : ℤ) * (M.F : ℤ) = 2 * (M.E : ℤ) := by exact_mod_cast faceRegular_pF M hF
  have hqv : (q : ℤ) * (M.V : ℤ) = 2 * (M.E : ℤ) := by exact_mod_cast vertexRegular_qV M hV
  have heuler : (M.V : ℤ) - (M.E : ℤ) + (M.F : ℤ) = 2 := hsphere.2
  have hElt : (1 : ℤ) ≤ (M.E : ℤ) := by exact_mod_cast hE
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have key : (M.E : ℤ) * (2 * p + 2 * q - p * q) = 2 * (p * q) := by
    linear_combination (-(q : ℤ)) * hpf - (p : ℤ) * hqv + ((p : ℤ) * q) * heuler
  have hgoal : (p : ℤ) * q < 2 * p + 2 * q := by
    nlinarith [key, hElt, mul_pos hp' hq']
  exact_mod_cast hgoal

/-- **The five Platonic types.** A regular sphere map with face length `p ≥ 3` and vertex
degree `q ≥ 3` (with at least one edge) has `(p, q)` equal to one of the five Platonic
pairs: `(3,3)` tetrahedron, `(3,4)` cube, `(4,3)` octahedron, `(3,5)` dodecahedron,
`(5,3)` icosahedron. This is Chapter 12, derived from Euler's formula. -/
theorem platonic_pairs (M : CombMap D) (hsphere : M.IsSphereMap)
    {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hE : 0 < M.E)
    (hF : M.FaceRegular p) (hV : M.VertexRegular q) :
    (p = 3 ∧ q = 3) ∨ (p = 3 ∧ q = 4) ∨ (p = 4 ∧ q = 3) ∨
      (p = 3 ∧ q = 5) ∨ (p = 5 ∧ q = 3) := by
  have hc : p * q < 2 * p + 2 * q :=
    platonic_constraint M hsphere (by omega) (by omega) hE hF hV
  have hpb : p ≤ 5 := by nlinarith [hc, hq, hp]
  have hqb : q ≤ 5 := by nlinarith [hc, hp, hq]
  interval_cases p <;> interval_cases q <;> omega

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


open ProofsInTheBook.Chapter12
open ProofsInTheBook.PlanarMap

theorem solution {D : Type*} [Fintype D] [DecidableEq D] (M : CombMap D)
    (hsphere : M.IsSphereMap) {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hE : 0 < M.E)
    (hF : M.FaceRegular p) (hV : M.VertexRegular q) :
    (p = 3 ∧ q = 3) ∨ (p = 3 ∧ q = 4) ∨ (p = 4 ∧ q = 3) ∨
      (p = 3 ∧ q = 5) ∨ (p = 5 ∧ q = 3) :=
  CombMap.platonic_pairs M hsphere hp hq hE hF hV
