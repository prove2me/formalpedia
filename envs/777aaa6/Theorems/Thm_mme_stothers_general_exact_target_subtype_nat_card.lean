-- Prove2me | Theorems.Thm_mme_stothers_general_exact_target_subtype_nat_card
-- name    : mme_stothers_general_exact_target_subtype_nat_card
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T05:14:51.798012+00:00
-- url     : https://prove2.me/theorems/a1fb6db6-29f6-4fa0-b7e6-921bbe7aebd8
-- title:
--   Multinomial count of general exact-profile addresses
-- statement:
--   **Exact count of the target addresses at an arbitrary integral profile.**
--
--   Fix an integral ten-class profile $\beta$ and a scale $m$, and put $N = 3Dm$ with
--   $D=\sum_i n_i \beta_i$. Among the marginal-supported outer addresses of length $N$, those whose
--   $45$-cell joint histogram is exactly the prescribed one are counted by the multinomial
--   coefficient
--
--   $$\bigl|\{a : \text{exact joint profile}\}\bigr| \;=\; \frac{N!}{\prod_{\sigma} \bigl(T_\sigma\bigr)!},$$
--
--   the product running over the $45$ supported ordered grade triples, with $T_\sigma$ the prescribed
--   multiplicity of $\sigma$.
--
--   The point is that an address is determined by the word of joint types it realizes, one supported
--   triple per position, and the prescribed histogram says exactly which words are allowed: the
--   number of such words is the multinomial coefficient of the histogram. The two directions of that
--   correspondence use that the prescribed multiplicity of an unsupported triple is zero, so no
--   information is lost in restricting attention to the $45$ supported cells, and that an exact-profile
--   address is automatically marginally regular.
--
--   Together with the factorization $N!/\prod_\sigma T_\sigma! = \bigl(N!/\prod_j M_j!\bigr)\cdot
--   D_*$, where $D_*=\prod_j M_j!/\prod_\sigma T_\sigma!$ is the star degree, this is the numerator of
--   the target-to-ambient ratio that governs how many addresses survive the outer hash. At the fixed
--   witness it specializes to the published count.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3 and Section 5, Equation (5.2); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_exact_target_subtype_nat_card
    (base : Fin 10 → ℕ) (m : ℕ) :
    Nat.card
        {a : MME.StothersFourth.GenMarginalSupportedAddress base m //
          MME.StothersFourth.GenHasExactJointProfile a} =
      (MME.StothersFourth.genOuterLength base m).factorial /
        ∏ sigma : MME.StothersFourth.GenHashSupportTriple,
          (MME.StothersFourth.genHashTargetJointTable base m sigma).factorial := by
  sorry
