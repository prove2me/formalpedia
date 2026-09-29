-- Prove2me | Theorems.Thm_mme_stothers_general_exact_target_count_factorization
-- name    : mme_stothers_general_exact_target_count_factorization
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T05:16:35.599158+00:00
-- url     : https://prove2.me/theorems/ad9e0558-cc87-4def-8cac-394ea5c75e09
-- title:
--   Target count as ambient multinomial times star degree
-- statement:
--   **Target count factors as ambient multinomial times star degree, at any profile.**
--
--   Fix an integral ten-class profile $\beta$ and a scale $m$, and put $N=3Dm$. Write
--   $M_j = M_j(\beta)m$ for the nine marginal counts and $T_\sigma$ for the prescribed multiplicity of
--   the supported grade triple $\sigma$. Set
--
--   $$V \;=\; \frac{N!}{\prod_{j} M_j!},\qquad
--   D_* \;=\; \frac{\prod_j M_j!}{\prod_\sigma T_\sigma!}.$$
--
--   Then the number of exact-profile addresses is exactly $V\,D_*$, and $D_*\ge 1$.
--
--   Here $V$ is the number of arrangements of a single mode word with the prescribed letter counts,
--   and $D_*$ is the *star degree*: the number of ways to complete one such word to a full address
--   with the prescribed joint histogram. That $D_*$ is a natural number at all -- that
--   $\prod_\sigma T_\sigma!$ divides $\prod_j M_j!$ -- is the combinatorial content, and it follows by
--   grouping the supported triples according to their first coordinate: within the group over grade
--   $j$ the multiplicities sum to $M_j$, so their factorials divide $M_j!$. That $D_*\ge1$ is then
--   immediate, and expresses that the joint histogram is at least as constrained as its marginal.
--
--   This factorization is what turns the target count into the product of an ambient count and a
--   degree, and the ratio $D_*(\text{profile})/D_*(\text{max-entropy profile on the same fibre})$ is
--   the combination loss of Equation (3.4). At the fixed witness it specializes to the published
--   factorization.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3 and Equations (3.2)-(3.4); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_exact_target_count_factorization
    (base : Fin 10 → ℕ) (m : ℕ) :
    let N := MME.StothersFourth.genOuterLength base m
    let V : ℝ :=
      (N.factorial : ℝ) /
        ∏ j : Fin 9,
          ((MME.StothersFourth.genMarginalCount base m j).factorial : ℝ)
    (Nat.card
        {a : MME.StothersFourth.GenMarginalSupportedAddress base m //
          MME.StothersFourth.GenHasExactJointProfile a} : ℝ) =
        V * (MME.StothersFourth.genHashTargetStarDegree base m : ℝ) ∧
      1 ≤ MME.StothersFourth.genHashTargetStarDegree base m := by
  sorry
