-- Prove2me | Definitions.Def_Hirsch_scalar_fiber_model
-- name    : Hirsch_scalar_fiber_model
-- status  : Definition
-- author  : @jjosh
-- created : 2026-09-08T16:37:37.235308+00:00
-- url     : https://prove2.me/theorems/59af3151-06aa-45f7-a758-293ca1fc5a83
-- title:
--   Common affine-height fibers, endpoint walks, and finite vertex/edge covers
-- statement:
--   Definitions for common scalar-height fibers of finitely many Euclidean factor sets; fixed-endpoint padded graph walks; strictly height-decreasing edge walks; and explicit finite covers witnessing upper bounds on the number of vertices and undirected edges.
-- source:
--   Definitions introduced to formalize the scalar-fiber obstruction arguments in jjoshua2/prove2me-work PR #11 (2026-09-08).

import Definitions.Def_Hirsch_model

set_option autoImplicit false
open scoped RealInnerProductSpace BigOperators

namespace Hirsch

/-- A fixed-endpoint padded walk in the vertex-edge graph of `P`.  Unlike
`DiamLE`, the endpoints are supplied explicitly. -/
def EndpointWalkLE {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) (B : ℕ) (u v : E) : Prop :=
  ∃ w : ℕ → E, w 0 = u ∧ w B = v ∧
    ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))

/-- The common-scalar-height fiber of finitely many factor sets. -/
def ScalarHeightFiber {k d : ℕ}
    (P : Fin k → Set (EuclideanSpace ℝ (Fin d)))
    (h : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ) :
    Set (Fin k → EuclideanSpace ℝ (Fin d)) :=
  {x | (∀ i, x i ∈ P i) ∧ ∀ i j, h i (x i) = h j (x j)}

/-- A genuine edge walk on which an affine height strictly decreases at every
step.  The `Fin (L+1)` indexing makes `L` the number of edges. -/
def StrictHeightEdgeWalk {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) (h : E →ᵃ[ℝ] ℝ) (L : ℕ) (u v : E) : Prop :=
  ∃ w : Fin (L + 1) → E,
    w ⟨0, Nat.zero_lt_succ L⟩ = u ∧
    w ⟨L, Nat.lt_succ_self L⟩ = v ∧
    (∀ j, w j ∈ P) ∧
    ∀ j : Fin L,
      Adj P (w (Fin.castSucc j)) (w (Fin.succ j)) ∧
      h (w (Fin.castSucc j)) > h (w (Fin.succ j))

/-- `VertexCover P m` means the extreme points of `P` can be listed using at
most `m` slots.  Duplicates are allowed, so this is convenient for upper bounds. -/
def VertexCover {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) (m : ℕ) : Prop :=
  ∃ vertices : Fin m → E,
    ∀ x ∈ Set.extremePoints ℝ P, ∃ j, vertices j = x

/-- `EdgeCover P m` means the undirected edges of `P` can be represented using
at most `m` oriented pairs.  Each representative itself must be a genuine edge;
either orientation may cover a requested edge. -/
def EdgeCover {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) (m : ℕ) : Prop :=
  ∃ edges : Fin m → E × E,
    (∀ j, Adj P (edges j).1 (edges j).2) ∧
    ∀ x y, Adj P x y → ∃ j, edges j = (x, y) ∨ edges j = (y, x)

end Hirsch


