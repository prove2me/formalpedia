-- Prove2me | Theorems.Thm_groupCohomology_subsingleton_H1_specialLinearGroup_fin_two_traceZero_algebra_of_charP_three
-- name    : groupCohomology.subsingleton_H1_specialLinearGroup_fin_two_traceZero_algebra_of_charP_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/b7b7f788-7ddf-5e20-9759-5e220ffe46a6
-- title:
--   Vanishing of H¹(SL₂(F),mathfraksl₂(k)) in characteristic 3
-- statement:
--   Let $F$ be a finite field of characteristic $3$ and let $k$ be a finite field equipped with an $F$-algebra structure. Let $A$ be an $F$-linear representation of $\mathrm{SL}_2(F)$, and suppose given an $F$-linear map $e$ from $A$ to the $2\times 2$ matrices over $k$ (the target being viewed as an $F$-module by restriction of scalars) subject to three conditions: $e$ is injective; the image of $e$ is exactly the $F$-submodule obtained by restricting scalars along $F \to k$ in the kernel of the $k$-linear trace map on $2\times 2$ matrices over $k$, i.e. $e$ identifies $A$ with the trace-zero matrices $\mathfrak{sl}_2(k)$ as an $F$-module; and $e$ is equivariant for conjugation, in the sense that for every $g \in \mathrm{SL}_2(F)$ and every $a \in A$ one has $e(\rho(g)a) = \bar g \, e(a) \, \overline{g^{-1}}$, where $\bar{\;\cdot\;}$ denotes entrywise application of the structure map $F \to k$ to the underlying matrix. The conclusion is that the first group cohomology $H^1(\mathrm{SL}_2(F), A)$ is a subsingleton, hence trivial.
--
--   This is the characteristic-$3$ case of the vanishing of $H^1(\mathrm{SL}_2(F),\mathfrak{sl}_2)$ for finite $F$, with coefficients extended from $F$ to a finite $F$-algebra field $k$; it is a special case of the cohomology computations of Cline, Parshall and Scott, and appears in the Darmon–Diamond–Taylor account of modularity lifting as Lemma 2.48. It is deduced from the case $k = F$ recorded in [`groupCohomology.subsingleton_H1_specialLinearGroup_fin_two_traceZero_of_charP_three`](thm.html#groupCohomology.subsingleton_H1_specialLinearGroup_fin_two_traceZero_of_charP_three), and is used in turn to prove the vanishing statement for the dual of the trace-zero representation, which enters the deformation-theoretic computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_subsingleton_H1_specialLinearGroup_fin_two_traceZero_algebra_of_charP_three.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix MatrixGroups groupCohomology

theorem groupCohomology.subsingleton_H1_specialLinearGroup_fin_two_traceZero_algebra_of_charP_three
    {F : Type} [Field F] [Finite F] [CharP F 3]
    {k : Type} [Field k] [Finite k] [Algebra F k]
    (A : Rep F SL(2, F)) (e : A →ₗ[F] Matrix (Fin 2) (Fin 2) k)
    (he_inj : Function.Injective e)
    (he_range : LinearMap.range e =
      (LinearMap.ker (Matrix.traceLinearMap (Fin 2) k k)).restrictScalars F)
    (he_act : ∀ (g : SL(2, F)) (a : A),
      e (A.ρ g a) = ((g : Matrix (Fin 2) (Fin 2) F).map (algebraMap F k)) * e a *
        (((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).map (algebraMap F k))) :
    Subsingleton (H1 A) := by sorry
