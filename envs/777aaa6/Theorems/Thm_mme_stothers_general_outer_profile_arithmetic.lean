-- Prove2me | Theorems.Thm_mme_stothers_general_outer_profile_arithmetic
-- name    : mme_stothers_general_outer_profile_arithmetic
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T05:08:26.813549+00:00
-- url     : https://prove2.me/theorems/cdedce1a-7a20-4293-a753-59a7b1ab0828
-- title:
--   Structural arithmetic of a general integral profile
-- statement:
--   **Structural arithmetic of an arbitrary integral ten-class profile.**
--
--   Four facts underlying the general-profile outer data. The first is about the ten Table-1
--   symmetry classes alone and involves no profile; the other three hold for every integral profile
--   $\beta:\{1,\dots,10\}\to\mathbb N$.
--
--   1. **The Equation (5.2) matrix counts orbit members by coordinate.** For every class $r$, every
--      mode $s\in\{1,2,3\}$ and every grade $j\in\{0,\dots,8\}$, the number of grade triples in the
--      permutation orbit of the class representative whose $s$-th coordinate equals $j$ is exactly the
--      $(r,j)$ entry of the integer matrix of Equation (5.2). In particular the count does not depend
--      on the mode $s$, as it must, the orbit being permutation-closed.
--
--   2. **Row sums.** $\sum_{j=0}^{8} M_j(\beta) = 3D$, where $M_j(\beta)$ are the nine-grade marginal
--      numerators and $D=\sum_i n_i\beta_i$. Equivalently: each row of the Equation (5.2) matrix sums
--      to $3n_r$, so the three mode words of an address of length $3D m$ do use every position.
--
--   3. **Agreement with $Q$.** $M_j(\beta) = (Q\beta)_j$ as real numbers, i.e. the integer marginal
--      numerators are literally the Equation (5.2) map applied to the unnormalized profile. This is
--      what connects the integral outer data to the real-valued marginal $A = \tfrac13 Qa$ used by
--      `globalRate`.
--
--   4. **The $45$-cell histogram has the prescribed marginals.** For every mode $i$ and grade $j$,
--
--   $$\sum_{\substack{\sigma\ \text{supported}\\ \sigma_i = j}} \text{(joint count of }\sigma) \;=\; M_j(\beta)\,m .$$
--
--   Together these say that the exact target histogram at any integral profile really is a joint
--   distribution on the $45$ supported grade triples with the prescribed nine-grade marginals, which
--   is the hypothesis under which the Lemma 5.2 entropy comparison applies. Item 1 is also an
--   independent consistency check between Table 1's ten permutation classes and the integer matrix
--   printed in Equation (5.2).
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5, Table 1 and Equation (5.2); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_outer_profile_arithmetic :
    (∀ (r : Fin 10) (s : Fin 3) (j : Fin 9),
      ((MME.StothersFourth.genClassOrbit r).filter
          (fun sigma ↦ sigma s = j)).card =
        MME.StothersFourth.genClassMarginalMultiplicity r j) ∧
    (∀ base : Fin 10 → ℕ,
      ∑ j : Fin 9, MME.StothersFourth.genMarginalBaseCount base j =
        3 * MME.StothersFourth.genProfileScale base) ∧
    (∀ (base : Fin 10 → ℕ) (j : Fin 9),
      (MME.StothersFourth.genMarginalBaseCount base j : ℝ) =
        MME.StothersFourth.Q (fun i ↦ (base i : ℝ)) j) ∧
    (∀ (base : Fin 10 → ℕ) (m : ℕ) (i : Fin 3) (j : Fin 9),
      (∑ sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
          sigma.1 i = j},
        MME.StothersFourth.genHashTargetJointTable base m sigma.1) =
          MME.StothersFourth.genMarginalCount base m j) := by
  sorry
