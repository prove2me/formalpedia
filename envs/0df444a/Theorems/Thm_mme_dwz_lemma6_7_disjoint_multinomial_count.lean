-- Prove2me | Theorems.Thm_mme_dwz_lemma6_7_disjoint_multinomial_count
-- name    : mme_dwz_lemma6_7_disjoint_multinomial_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T11:07:41.560334+00:00
-- url     : https://prove2.me/theorems/129d955c-1d6e-40f6-b7fe-2d5a8e57cc90
-- title:
--   DWZ Lemma 6.7: exact disjoint-region multinomial count
-- statement:
--   Let $R$ index finitely many pairwise-disjoint position regions, represented as tagged finite types $P_r$. For each region $r$, prescribe a finite list of nonnegative integer symbol multiplicities whose sum is $|P_r|$. A prescribed split is an ordered partition of that region into disjoint symbol-cells having exactly those multiplicities. Then the number of simultaneous prescribed splits over all regions is exactly
--
--   $$\prod_{r\in R}\binom{|P_r|}{c_{r,0},\ldots,c_{r,m_r-1}}.$$
--
--   This is the exact finite counting step behind DWZ Equation (23), before multinomial-to-entropy asymptotics and the typical-block denominator are introduced.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Section 6.2, Lemma 6.7 numerator count and Equation (23), printed pp. 54-56 (PDF pp. 55-57).

import Mathlib
import Definitions.Def_mme_dwz_prescribed_splits

open scoped BigOperators
open MME.DWZCompatibilityCount
set_option autoImplicit false

theorem mme_dwz_lemma6_7_disjoint_multinomial_count
    {R : Type*} [Fintype R]
    (Position : R → Type*)
    [∀ r, Fintype (Position r)] [∀ r, DecidableEq (Position r)]
    (counts : R → List ℕ)
    (hsize : ∀ r, (counts r).sum = Fintype.card (Position r)) :
    Nat.card
        (∀ r, PrescribedSplits (Finset.univ : Finset (Position r)) (counts r)) =
      ∏ r, Nat.multinomial Finset.univ
        (fun i : Fin (counts r).length => (counts r).get i) := by sorry
