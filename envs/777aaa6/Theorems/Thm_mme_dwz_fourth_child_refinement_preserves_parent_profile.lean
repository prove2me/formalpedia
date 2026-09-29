-- Prove2me | Theorems.Thm_mme_dwz_fourth_child_refinement_preserves_parent_profile
-- name    : mme_dwz_fourth_child_refinement_preserves_parent_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T08:46:10.749457+00:00
-- url     : https://prove2.me/theorems/692067bf-48bb-4f4f-a1c8-f21b42b51d16
-- title:
--   Child fine-coordinate refinements preserve a canonical fourth-power parent's prescribed Z profile
-- statement:
--   Let $q,m$ be nonnegative integers, let $L\in\{0,\ldots,8\}$ be a fourth-power coarse $Z$ grade, and let $p$ be an integral five-letter profile with positive denominator $D$ and counts $c_a$ summing to $D$. Put $N=Dm$.
--
--   At each position $r$, choose left and right square coarse grades $k_r,\ell_r\in\{0,\ldots,4\}$ with $k_r+\ell_r=L$. Choose two arbitrary pairs of canonical square coordinates $(x_r,y_r)$ and $(x'_r,y'_r)$ inside these same respective coarse classes, and join them to form fourth-power words $w,w'$.
--
--   Then
--   $$
--   w\text{ has parent profile }p
--   \quad\Longleftrightarrow\quad
--   \#\{r:k_r=a\}=m c_a\ \text{for every }a,
--   $$
--   and
--   $$
--   w\text{ has parent profile }p
--   \quad\Longleftrightarrow\quad
--   w'\text{ has parent profile }p.
--   $$
--
--   Thus changing the finer coordinates inside fixed child coarse blocks preserves the parent's exact prescribed-$Z$ test. This includes the empty-word case $m=0$.
--
--   **Formalization Note** This is a coordinate-support statement. It does not assert an induced tensor restriction, a retained-family cardinality bound, an entropy-loss estimate, or a matrix-multiplication value bound.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5, Section 3.5 (coarsening consecutive coordinate grades), Definition 3.7 (split distributions), and Definition 3.9 (restricted-splitting tensor power). Elementary coordinate-level consequence of these definitions for level-3/level-2 canonical CW partitions, not a separately named theorem in the paper.

import Definitions.Def_mme_dwz_fourth_child_coordinate_join_data

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue
open MME.CoupledParentCompatibility
universe u
set_option autoImplicit false

theorem mme_dwz_fourth_child_refinement_preserves_parent_profile (q : ℕ) (L : Fin 9)
    (p : IntegerZSplitProfile 5) (m : ℕ)
    (kLeft kRight : Fin (p.length m) → Fin 5)
    (hsum : ∀ r, (kLeft r).val + (kRight r).val = L.val)
    (x x' : (r : Fin (p.length m)) → LiftedCoarsePair.{u} q (kLeft r))
    (y y' : (r : Fin (p.length m)) → LiftedCoarsePair.{u} q (kRight r)) :
    let w := packWord (p.length m) (fun r =>
      joinCoords q L (kLeft r) (kRight r) (hsum r) (x r) (y r))
    let w' := packWord (p.length m) (fun r =>
      joinCoords q L (kLeft r) (kRight r) (hsum r) (x' r) (y' r))
    (prescribedZWord fourthLeftGrade p m w ↔
      ∀ a : Fin 5, (Finset.univ.filter (fun r => kLeft r = a)).card = p.count a * m) ∧
    (prescribedZWord fourthLeftGrade p m w ↔
      prescribedZWord fourthLeftGrade p m w') := by sorry
