-- Prove2me | Theorems.Thm_groupCohomology_H1pi_map_of_values
-- name    : groupCohomology.H1pi_map_of_values
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:38.141331+00:00
-- url     : https://prove2.me/theorems/60b26f1e-12ca-4fd5-a192-69009791604d
-- title:
--   A pointwise-compatible cocycle map sends one explicit cohomology class to the other
-- statement:
--   Let $k$ be a commutative ring, let $r:H→G$ be a group homomorphism, let $A$ be a $k$-representation of $G$, let $B$ be a $k$-representation of $H$, and let $φ:A|_H→B$ be an equivariant morphism. For cocycles $c$ on $A$ and $d$ on $B$, assume $φ(c(rσ))=d(σ)$ for every $σ∈H$. Then the induced map on first cohomology satisfies $$H^1(r,φ)([c])=[d].$$ This identifies mapped division classes from equality of their cocycle values.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open CategoryTheory
open groupCohomology

theorem groupCohomology.H1pi_map_of_values
    {k G H : Type} [CommRing k] [Group G] [Group H]
    (r : H →* G) (A : Rep k G) (B : Rep k H)
    (φ : Rep.res r A ⟶ B) (c : cocycles₁ A) (d : cocycles₁ B)
    (h : ∀ σ, φ.hom (c (r σ)) = d σ) :
    (groupCohomology.map r φ 1).hom (H1π A c) = H1π B d := by sorry
