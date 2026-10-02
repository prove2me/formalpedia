-- Prove2me | Theorems.Thm_BookSixth_rotTriple_legs_are_jointly_continuous
-- name    : BookSixth.rotTriple_legs_are_jointly_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T01:49:11.260976+00:00
-- url     : https://prove2.me/theorems/bed0817e-ba6d-437a-ba2b-047fe73fbf92
-- title:
--   Chapter 15: both legs of the standardising isotopy are jointly continuous
-- statement:
--   Let $R(t) = R_{12}(t\theta_3)\,R_{02}(t\theta_2)\,R_{01}(t\theta_1)$ be the threefold coordinate rotation of $\mathbb{R}^3$. Both legs of the standardising isotopy are jointly continuous in the time parameter and the point: the forward leg is $R(t) \cdot x + t \cdot a$, and the inverse leg is $R(t)^{\mathsf T} \cdot x - t \cdot (R(t)^{\mathsf T} \cdot a)$. The reason is that every entry of $R(t)$ is built from $\cos(t\theta)$ and $\sin(t\theta)$, hence is a continuous function of $t$, and matrix-vector multiplication and scalar multiplication are continuous. This is the third ingredient of `BookSixth.rotTriple_isotopy`; combined with the already-proved invertibility it shows that the isotopy $H\,t\,x = R(t)\,\cdot x + t \cdot a$ is a jointly continuous family of homeomorphisms of $\mathbb{R}^3$, i.e. a genuine isotopy rather than merely a pointwise family of homeomorphisms. Note the inverse leg carries the factor $t \cdot (R(t)^{\mathsf T} \cdot a)$, not $t \cdot a$: the transpose is a rotation, not the identity, so $R(t)^{\mathsf T} \cdot a \neq a$ in general.
-- source:
--   Proofs from THE BOOK, Chapter 15 (Aigner-Ziegler), geometric motion of perfect circles; joint continuity of the forward and inverse legs of the standardising isotopy.

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3
import Definitions.Def_BookSixthRotTriple
open scoped BigOperators
open scoped Matrix
open BookSixth Matrix

theorem BookSixth.rotTriple_legs_are_jointly_continuous (θ1 θ2 θ3 : ℝ) (a : Fin 3 → ℝ) :
    (Continuous fun p : ℝ × (Fin 3 → ℝ) =>
      rotTriple p.1 θ1 θ2 θ3 p.2 + p.1 • a) ∧
    (Continuous fun p : ℝ × (Fin 3 → ℝ) =>
      (rot12Matrix (p.1 * θ3) * rot02Matrix (p.1 * θ2) * rot01Matrix (p.1 * θ1))ᵀ *ᵥ p.2
        - p.1 • ((rot12Matrix (p.1 * θ3) * rot02Matrix (p.1 * θ2)
            * rot01Matrix (p.1 * θ1))ᵀ *ᵥ a)) := by sorry
