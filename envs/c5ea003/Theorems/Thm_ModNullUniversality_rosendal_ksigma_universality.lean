-- Prove2me | Theorems.Thm_ModNullUniversality_rosendal_ksigma_universality
-- name    : ModNullUniversality.rosendal_ksigma_universality
-- status  : Open
-- author  : @username
-- created : 2026-11-09T09:01:25.083843+00:00
-- url     : https://prove2.me/theorems/c25a9dbe-9341-404b-a05c-8d92c465c256
-- title:
--   Rosendal's $K_\sigma$ universality benchmark
-- statement:
--   Every equivalence relation with a $K_\sigma$ graph on a Polish space Borel reduces to the bounded-difference relation on real sequences:
--
--   $$x\mathrel{\ell_\infty}y\quad\Longleftrightarrow\quad
--   \exists M\in\mathbb R\ \forall n\in\mathbb N\ |x(n)-y(n)|\le M.$$
--
--   The source measurable structure is its Borel sigma algebra. The reduction is one measurable map whose equivalence identity holds for all source pairs. This is the universality consequence of Rosendal's Theorem 17 and Proposition 19. It does not assert that the displayed relation on all of $\mathbb R^{\mathbb N}$ has a $K_\sigma$ graph in that presentation.
-- source:
--   C. Rosendal, Cofinal families of Borel equivalence relations and quasiorders, J. Symbolic Logic 70 (2005), 1325–1340, Theorem 17 (p. 1333) and Proposition 19 (p. 1334), universality consequence. https://homepages.math.uic.edu/~rosendal/PapersWebsite/CofinalFamilies.pdf

import Definitions.Def_ModNullCore20261109

set_option autoImplicit false

theorem ModNullUniversality.rosendal_ksigma_universality
    (X : Type) [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (E : Setoid X)
    (hE : ModNullUniversality.IsKSigma {p : X × X | E.r p.1 p.2}) :
    ModNullUniversality.BorelReducible E.r ModNullUniversality.LInfinityRelation := by sorry
