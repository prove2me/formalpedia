-- Prove2me | Theorems.Thm_BookSixth_small_displacement_is_homeomorph
-- name    : BookSixth.small_displacement_is_homeomorph
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-26T08:58:31.708779+00:00
-- url     : https://prove2.me/theorems/5f342cbf-e04b-4e47-b598-dafa8fe75f19
-- title:
--   Chapter 15: a map with small Lipschitz displacement is a homeomorphism
-- statement:
--   Let $S$ be a continuous map of $\mathbb{R}^3$ whose displacement $S(x) - x$ is Lipschitz with a constant $q < 1$. Then $S$ is a homeomorphism of $\mathbb{R}^3$, its inverse is Lipschitz, and $S$ moves no two points closer together by more than a factor $1 - q$. This is the analytic core of the Lipschitz-bump construction of an ambient isotopy: one starts with a continuous motion of a family of disjoint round circles, cuts it off near each circle by a bump function equal to one there, and needs the resulting perturbation of the identity to be a homeomorphism. Here the map is only required to be a small displacement, not a similarity, which is what allows the construction to move one circle while leaving the others fixed.
-- source:
--   Analytic core of the ambient-extension step in the roundness-preserving motion of Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15, following the Freedman-Skora construction described in Brendle and Hatcher, "Configuration spaces of shrinking round circles in R^3", Section 2. The construction is $F(x) = x + \sum_i \chi_i(x)\,\bigl(S_i(x) - x\bigr)$, where the $\chi_i$ are Lipschitz bumps supported in disjoint neighbourhoods of the circles, equal to one on the corresponding circle. Its displacement $E(x) = F(x) - x$ is then Lipschitz with a constant that can be made smaller than $1$ by choosing the bumps small, and the lemma above turns $F$ into a homeomorphism.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.small_displacement_is_homeomorph (q : ℝ) (hq : 0 ≤ q ∧ q < 1)
    (S : Space3 → Space3) (hcont : Continuous S)
    (hlip : ∀ x y : Space3, ‖(S x - x) - (S y - y)‖ ≤ q * ‖x - y‖) :
    ∃ Sinv : Space3 → Space3,
      Continuous Sinv ∧ Function.LeftInverse Sinv S ∧ Function.RightInverse Sinv S ∧
        ∀ x y : Space3, ‖x - y‖ ≤ (1 - q)⁻¹ * ‖S x - S y‖ := by sorry
