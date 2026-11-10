-- Prove2me | Theorems.Thm_ModNullUniversality_fsigma_conull_universality
-- name    : ModNullUniversality.fsigma_conull_universality
-- status  : Open
-- author  : @username
-- created : 2026-11-09T09:01:54.776895+00:00
-- url     : https://prove2.me/theorems/e41ab9b4-80f5-4291-8cba-e0c2cf6df28c
-- title:
--   Proposition 6.1 — invariant-conull $F_\sigma$ universality
-- statement:
--   For every $F_\sigma$ equivalence relation $E$ on a Polish space $X$ and every Borel probability measure $\mu$ on $X$, there is an $E$-invariant Borel set $D\subseteq X$ of measure one such that
--
--   $$E\mathbin{\upharpoonright}D\ \leq_B\ \ell_\infty.$$
--
--   Invariance means that $E$-equivalent points have the same membership in $D$. The reducing map is measurable on the inherited subtype sigma algebra, and its equivalence identity holds for every pair of points of $D$. The chosen domain and map may depend on both $E$ and $\mu$.
-- source:
--   Universality modulo null sets in the Borel hierarchy, user-supplied unpublished manuscript dated 9 November 2026; SHA-256 48745c75427f83370292c2e4cf91ec06377e80472252db0182599edcd05e2d97, Proposition 6.1, source lines 417–422, and its proof.

import Definitions.Def_ModNullCore20261109

set_option autoImplicit false

theorem ModNullUniversality.fsigma_conull_universality
    (X : Type) [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (E : Setoid X)
    (hE : ModNullUniversality.IsFSigma {p : X × X | E.r p.1 p.2}) :
    ∃ D : Set X, MeasurableSet D ∧ μ D = 1 ∧
      ModNullUniversality.IsInvariant E.r D ∧
      ModNullUniversality.BorelReducible
        (fun x y : D => E.r x.val y.val) ModNullUniversality.LInfinityRelation := by sorry
