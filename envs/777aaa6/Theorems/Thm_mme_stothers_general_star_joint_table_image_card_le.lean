-- Prove2me | Theorems.Thm_mme_stothers_general_star_joint_table_image_card_le
-- name    : mme_stothers_general_star_joint_table_image_card_le
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T05:25:22.03856+00:00
-- url     : https://prove2.me/theorems/feaeb78e-cc95-466c-97c4-550880f39da5
-- title:
--   Joint histograms realized on a completion star
-- statement:
--   **How many joint histograms a completion star can realize.**
--
--   Fix an integral ten-class profile $\beta$, a scale $m$, an ambient family $E$ of
--   marginal-supported addresses of length $N=3Dm$, one address $a$, and a mode $i$. Consider the
--   *star* of $a$ at $i$: the members of $E$ that share $a$'s $i$-th mode word. Each of them has a
--   $45$-cell joint histogram, and
--
--   $$\#\{\text{histograms realized on the star}\} \;\le\; (N+1)^{45}.$$
--
--   The bound is crude and purely dimensional: a histogram assigns to each of the $45$ supported grade
--   triples a count between $0$ and $N$, so there are at most $(N+1)^{45}$ of them in total,
--   irrespective of any marginal constraint. It is what allows the star to be split into polynomially
--   many histogram fibres, each of which is then bounded separately; the product of the two bounds is
--   polynomial in $N$ times a single star degree, which is all the hashing argument needs.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3 and Equations (3.2)-(3.4); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_star_joint_table_image_card_le
    (base : Fin 10 → ℕ) (m : ℕ)
    (E : Finset (MME.StothersFourth.GenMarginalSupportedAddress base m))
    (a : MME.StothersFourth.GenMarginalSupportedAddress base m) (i : Fin 3) :
    ((E.filter (fun b ↦ b.1 i = a.1 i)).image
      MME.StothersFourth.genHashJointTable).card ≤
        (MME.StothersFourth.genOuterLength base m + 1) ^ 45 := by
  sorry
