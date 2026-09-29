-- Prove2me | Theorems.Thm_Coxeter_card_orbit_lt_of_not_generic
-- name    : Coxeter.card_orbit_lt_of_not_generic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:22:56.885276+00:00
-- url     : https://prove2.me/theorems/ec463012-0868-43d1-acd0-3e95f7d7ba6d
-- title:
--   Contrarian sharpness: genericity is necessary.
-- statement:
--   **Contrarian sharpness: genericity is necessary.**  At a *non*-generic (non-regular) point,
--   the vertex count is *strictly smaller* than `|W|`.  Thus the bare statement "count `= |W|`"
--   fails without the genericity hypothesis — a family of counterexamples to the ungeneric claim.
--
--   ```lean
--   theorem Coxeter.card_orbit_lt_of_not_generic[Finite W] {a : α}
--       (h : ¬ IsGeneric (W := W) a) : Nat.card (orbit W a) < Nat.card W := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/CoxeterPermutahedronPersistentSimplices.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/CoxeterPermutahedronPersistentSimplices.lean#L95

-- Thm stub generated from Novelty/CoxeterPermutahedronPersistentSimplices.lean
import Mathlib
import Definitions.Def_Novelty_CoxeterPermutahedronPersistentSimplices

/-!
# Persistent maximal simplices and the order of a finite Coxeter group

## Mission

*Conjecture (Persistent Maximal Simplices Count Equals Order of the Coxeter Group).*
For any finite Coxeter group `W` and any generic point `a` in the fundamental chamber, the
number of maximal *persistent* simplices in the canonical subdivision of the Coxeter
permutahedron `Pᵂ(a)` equals `|W|`, via a bijection with the group elements, independently
of the chosen generic `a`.

The full statement involves the geometry of the reflection representation, the canonical
subdivision of the permutahedron, and a persistence filtration — none of which are available
in `Mathlib`.  This file isolates and proves the **combinatorial and group-theoretic core**
on which the conjecture rests, in a self-contained way, together with a concrete instance for
the type `A` Coxeter groups (symmetric groups).

## What is actually proved

We work with an arbitrary finite group `W` acting on a set `α`.  A finite Coxeter group acting
on its reflection representation `α = V` is the motivating instance; the "fundamental chamber"
picks out points, and **a point of the open fundamental chamber is exactly a point with trivial
stabilizer** (a *regular* point).  We call such a point *generic* and model it by
`IsGeneric a : stabilizer W a = ⊥`.

The vertices of the Coxeter permutahedron `Pᵂ(a) = conv(W · a)` are exactly the orbit `W · a`
(for a regular `a` all orbit points are extreme).  Hence "vertices ↔ group elements" and, via
the paper's structural bijection "maximal persistent simplices ↔ vertices", the count is `|W|`.

* `Coxeter.orbitEquivGroup` — for a generic point, the orbit (vertex set) is in bijection
  with `W`.
* `Coxeter.card_orbit_of_generic` — the vertex count equals `Nat.card W = |W|`.
* `Coxeter.card_orbit_independent_of_point` — the count is the same for **any** two generic
  points: independence of the specific generic `a`.
* `Coxeter.card_orbit_mul_card_stabilizer` — the exact orbit–stabilizer factorisation, valid
  for *every* point.
* `Coxeter.card_orbit_lt_of_not_generic` — **contrarian sharpness / near-counterexample:**
  genericity is *necessary*.  At a non-generic (non-regular) point the count is strictly
  smaller than `|W|`, so the naive "count `= |W|`" statement is *false* without the
  genericity hypothesis.
* `Coxeter.persistent_simplices_count` — the conjecture's logical skeleton: any type `PS`
  of maximal persistent simplices that is in bijection with the vertex set of a generic
  permutahedron has cardinality `|W|`.

## Type `A` instance (symmetric groups)

`Sₙ = Equiv.Perm (Fin n)` is the Coxeter group of type `Aₙ₋₁`, with `|Sₙ| = n!`.  Its
permutahedron is the convex hull of the coordinate permutations of a vector `v : Fin n → ℝ`,
and a vector with distinct entries is a regular point.

* `Coxeter.symmetricGroup_order` — `|Sₙ| = n!`.
* `Coxeter.perm_fixes_iff_eq_one` — a vector with distinct entries is regular: only the
  identity permutation fixes it (concrete "generic ⇒ trivial stabilizer").
* `Coxeter.card_permutahedron_vertices` — the permutahedron of such a vector has exactly
  `n!` vertices, matching `|Sₙ|`.
-/

open Coxeter

open MulAction

variable {W : Type*} [Group W] {α : Type*} [MulAction W α]

theorem Coxeter.card_orbit_lt_of_not_generic[Finite W] {a : α}
    (h : ¬ IsGeneric (W := W) a) : Nat.card (orbit W a) < Nat.card W := by sorry
