-- Prove2me | Definitions.Def_Hirsch_recursive_projective_products
-- name    : Hirsch_recursive_projective_products
-- status  : Definition
-- author  : @jjosh
-- created : 2026-09-12T18:45:57.976842+00:00
-- url     : https://prove2.me/theorems/3c29c70d-337c-4d63-8f52-9c437f52e878
-- title:
--   Recursive positive projective product geometry certificates
-- statement:
--   Let $P$ be described by $n$ real linear inequalities in $\mathbb R^d$.
--   Suppose it has a finite recursive geometric certificate built from the following operations.
--   A leaf is a bounded H-polyhedron with at most three excess describing rows.
--   An affine step transports a certificate through an affine equivalence without
--   changing the dimension or number of rows. At a split, an invertible linear
--   coordinate map and a partition of all rows identify a source with a Cartesian
--   product of at least two positive-dimensional certified factors. Each factor's
--   row count is at least its dimension. A positive projective map
--   $x\mapsto x/(1+c\cdot x)$ then sends this source onto the parent with sheared
--   rows $a_i+b_i c$; both forward and inverse denominators are required positive
--   on their full feasible sets. Different nodes may use different charts.
--
--   This definition contains geometric data only; its diameter consequence is a separate theorem.
-- source:
--   Derived geometric certificate criterion; https://github.com/jjoshua2/prove2me-work/blob/fcbb02425dececaa9a8f7abd90c341ae99dbafac/research/RECURSIVE_PROJECTIVE_DISCOVERY_2026-09-12.md sections 1-3; classical projective invariance and product graph additivity are reused, not claimed novel.

import Mathlib
import Definitions.Def_Hirsch_model

/-! Finite geometric certificates for recursive projective product routing.
Only geometric data appear in constructors; no graph-distance premise occurs.
Each proper split uses every row and every coordinate exactly once. -/
open Set Hirsch
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
noncomputable section
namespace HirschRecursiveProducts

/-- A finite geometry certificate, not a diameter hypothesis. Proper positive-
dimensional factors prevent a split from merely restating the same instance.
Affine steps cover translations/recentering without changing n or d. -/
inductive ProductTree : {d n : ℕ} →
    (Fin n → EuclideanSpace ℝ (Fin d)) → (Fin n → ℝ) → Prop
  | leaf {d n : ℕ}
      {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
      (hbd : Bornology.IsBounded (Hpoly a b)) (hcount : n ≤ d + 3) :
      ProductTree a b
  | affine {d n : ℕ}
      {a a' : Fin n → EuclideanSpace ℝ (Fin d)} {b b' : Fin n → ℝ}
      (f : EuclideanSpace ℝ (Fin d) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin d))
      (himage : f '' Hpoly a b = Hpoly a' b')
      (prior : ProductTree a b) : ProductTree a' b'
  | split {d n k : ℕ}
      (dims counts : Fin k → ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
      (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
        (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
      (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
      (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
      (hrows : ∀ z i j, ⟪a (e ⟨i,j⟩), T.symm z⟫ = ⟪A i j, z i⟫)
      (hcount : ∀ i, dims i ≤ counts i)
      (hk : 2 ≤ k) (hdim : ∀ i, 0 < dims i)
      (c : EuclideanSpace ℝ (Fin d))
      (hsource : ∀ x ∈ Hpoly a b, 0 < 1 + ⟪c, x⟫)
      (htarget : ∀ y ∈ Hpoly (fun i => a i + b i • c) b, 0 < 1 + -⟪c, y⟫)
      (children : ∀ i, ProductTree (A i) (fun j => b (e ⟨i,j⟩))) :
      ProductTree (fun i => a i + b i • c) b

end HirschRecursiveProducts


