-- Prove2me | Theorems.Thm_groupCohomology_subsingleton_H1_specialLinearGroup_fin_two_traceZero_of_charP_three
-- name    : groupCohomology.subsingleton_H1_specialLinearGroup_fin_two_traceZero_of_charP_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/d34a3048-f89d-582d-8255-3f62f37274e7
-- title:
--   Vanishing of H¹(SL₂(F),mathfraksl₂) in characteristic three
-- statement:
--   Let $F$ be a finite field of characteristic $3$, and let $A$ be an $F$-linear representation of the group $\mathrm{SL}(2,F)$, i.e. an object of `Rep F SL(2, F)`. Suppose given an $F$-linear map $e$ from $A$ to the space of $2 \times 2$ matrices over $F$ such that: $e$ is injective; the range of $e$ is exactly the kernel of the trace, viewed as the $F$-linear map `Matrix.traceLinearMap (Fin 2) F F`, that is, the space of trace-zero $2\times 2$ matrices; and $e$ is equivariant for conjugation, in the sense that for every $g \in \mathrm{SL}(2,F)$ and every $a \in A$ one has $e(\rho_A(g)\,a) = g\, e(a)\, g^{-1}$, where $g$ and $g^{-1}$ are taken as matrices via the inclusion of $\mathrm{SL}(2,F)$ into $2\times 2$ matrices. Then the first group cohomology $H^1(A)$ of $\mathrm{SL}(2,F)$ with coefficients in $A$ is a subsingleton, i.e. it vanishes. In other words, any representation of $\mathrm{SL}(2,F)$ that is $F$-linearly isomorphic, equivariantly for the conjugation action, to the adjoint representation $\mathfrak{sl}_2(F)$ on trace-zero matrices has vanishing $H^1$.
--
--   This is the characteristic-$3$ case of the vanishing statement $H^1(\mathrm{SL}_2(\mathbb{F}),\operatorname{End}^0(\mathbb{F}^2)) = 0$ for finite fields of odd characteristic with $\#\mathbb{F} \neq 5$ (Lemma 2.48 of Darmon–Diamond–Taylor, a special case of the computations of Cline, Parshall and Scott), the only case needed in the deformation-theoretic argument there. It is applied through the variant [`groupCohomology.subsingleton_H1_specialLinearGroup_fin_two_traceZero_algebra_of_charP_three`](thm.html#groupCohomology.subsingleton_H1_specialLinearGroup_fin_two_traceZero_algebra_of_charP_three), which packages the same conclusion for coefficients presented as a matrix algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_subsingleton_H1_specialLinearGroup_fin_two_traceZero_of_charP_three.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix MatrixGroups groupCohomology

theorem groupCohomology.subsingleton_H1_specialLinearGroup_fin_two_traceZero_of_charP_three
    {F : Type} [Field F] [Finite F] [CharP F 3]
    (A : Rep F SL(2, F)) (e : A →ₗ[F] Matrix (Fin 2) (Fin 2) F)
    (he_inj : Function.Injective e)
    (he_range : LinearMap.range e = LinearMap.ker (Matrix.traceLinearMap (Fin 2) F F))
    (he_act : ∀ (g : SL(2, F)) (a : A),
      e (A.ρ g a) = (g : Matrix (Fin 2) (Fin 2) F) * e a * ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) :
    Subsingleton (H1 A) := by sorry
