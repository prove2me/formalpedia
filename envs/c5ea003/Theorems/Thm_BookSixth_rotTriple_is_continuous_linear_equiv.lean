-- Prove2me | Theorems.Thm_BookSixth_rotTriple_is_continuous_linear_equiv
-- name    : BookSixth.rotTriple_is_continuous_linear_equiv
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T01:23:12.610997+00:00
-- url     : https://prove2.me/theorems/6936ab09-a343-4422-bced-8f809a922ccf
-- title:
--   Chapter 15: the threefold coordinate rotation is a continuous linear equivalence
-- statement:
--   For every $t$ the threefold coordinate rotation $R(t) = R_{12}(t\theta_3) R_{02}(t\theta_2) R_{01}(t\theta_1)$ of $\mathbb{R}^3$ is a continuous linear equivalence, and its inverse is the transpose $R(t)^{\mathsf T}$ of the same matrix. Concretely there is a $\mathbb R$-linear isomorphism $E$ of $\mathbb{R}^3$ whose value is $R(t) \cdot$ and whose inverse value is $R(t)^{\mathsf T} \cdot$. Orthogonality of the three factors, proved in `BookSixth.rotTriple_transpose_mul_one`, makes $R(t)$ injective; a finite-dimensional injective linear map is surjective, so it is a continuous linear equivalence. Its inverse is the transpose because $R(t)^{\mathsf T} R(t) = I$. This is the second algebraic step needed by `BookSixth.rotTriple_isotopy`: it is what makes the inverse leg of the isotopy explicit, namely $(H\,t)^{-1} y = R(t)^{\mathsf T} y - t (R(t)^{\mathsf T} a)$, a jointly continuous function of $(t, y)$.
-- source:
--   Proofs from THE BOOK, Chapter 15 (Aigner-Ziegler), geometric motion of perfect circles; the continuous-linear-equivalence form of the threefold coordinate rotation, used by the standardising isotopy.

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3
import Definitions.Def_BookSixthRotTriple
open scoped BigOperators
open scoped Matrix
open BookSixth Matrix

theorem BookSixth.rotTriple_is_continuous_linear_equiv (θ1 θ2 θ3 t : ℝ) :
    ∃ E : (Fin 3 → ℝ) ≃SL[RingHom.id ℝ] (Fin 3 → ℝ),
      (∀ x, E x = rotTriple t θ1 θ2 θ3 x) ∧
      (∀ x, E.symm x = (rot12Matrix (t * θ3) * rot02Matrix (t * θ2) * rot01Matrix (t * θ1))ᵀ *ᵥ x) := by sorry
