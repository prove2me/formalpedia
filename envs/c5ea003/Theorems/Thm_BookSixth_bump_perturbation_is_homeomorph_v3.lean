-- Prove2me | Theorems.Thm_BookSixth_bump_perturbation_is_homeomorph_v3
-- name    : BookSixth.bump_perturbation_is_homeomorph_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T20:20:23.661886+00:00
-- url     : https://prove2.me/theorems/2691f203-4be1-4bb2-a275-3ab226cf43e8
-- title:
--   A finite sum of cut-off-scaled displacements is a homeomorphism whenever its Lipschitz constant is below one
-- statement:
--   Let $X$ be a complete normed space, let $\chi_i : X \to \mathbb R$ be scalar-valued cut-off functions and $S_i : X \to X$ continuous maps, and suppose that the summed displacement field $E(x) = \sum_i \chi_i(x)\,\bigl(S_i(x) - x\bigr)$ is Lipschitz with constant $q < 1$. Then the map $F(x) = x + E(x)$ is a homeomorphism of $X$ with a continuous inverse, and it satisfies the displayed formula for $F$.
--
--   This is the corrected cut-off patching criterion used to extend a small motion of a finite family of round circles to an ambient isotopy. The earlier version `BookSixth.bump_perturbation_is_homeomorph_v2` assumes $\sum_i (2L_i + M_i) < 1$ together with a bound $\|\chi_i x\| \le L_i$. That hypothesis is unusable in the intended application: a cut-off which equals $1$ on a component of the family forces $L_i \ge 1$, so the criterion would require $2 < 1$. The present statement instead bounds the Lipschitz constant of the summed displacement field directly. That is the quantity which actually tends to zero as the motion is subdivided in time, since the cut-off constant $c = 1/\delta$ is fixed while the displacement magnitude $M$ shrinks, and it is exactly what `BookSixth.small_displacement_is_homeomorph` consumes.
-- source:
--   Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The definitions (Space3) are from the definition module `Definitions.Def_BookSixth`. The analytic estimate supplying `hlipE` is `BookSixth.bump_perturbation_lipschitz_v2` (00c3e7a7) in its crude per-summand form, and `BookSixth.smul_lipschitz_bound` (d456c9e2) in its sharp form, giving the constant $cM + CL$ with $c = 1/\delta$ the cut-off Lipschitz constant and $C = 1$. The conclusion follows by instantiating `BookSixth.small_displacement_is_homeomorph` (5f342cbf) at $S_0(x) = x + E(x)$.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.bump_perturbation_is_homeomorph_v3 (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3)
    (hchi : ∀ i, LipschitzWith 1 (chi i))
    (hS : ∀ i, LipschitzWith 1 (S i))
    (hlipE : ∀ x y : Space3,
      ‖(∑ i, chi i x • (S i x - x)) - ∑ i, chi i y • (S i y - y)‖ ≤ q * ‖x - y‖) :
    ∃ F : Space3 → Space3,
      Continuous F ∧
      ∃ Finv : Space3 → Space3, Continuous Finv ∧
        (∀ x, Finv (F x) = x) ∧ (∀ x, F (Finv x) = x) ∧
        (∀ x, F x = x + ∑ i, chi i x • (S i x - x)) := by sorry
