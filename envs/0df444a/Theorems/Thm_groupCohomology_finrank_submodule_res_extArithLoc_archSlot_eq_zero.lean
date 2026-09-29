-- Prove2me | Theorems.Thm_groupCohomology_finrank_submodule_res_extArithLoc_archSlot_eq_zero
-- name    : groupCohomology.finrank_submodule_res_extArithLoc_archSlot_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/3b2b8e3f-7acc-56be-a551-875e6da63d79
-- title:
--   Vanishing rank of submodules of the archimedean slot H¹
-- statement:
--   Let $p$ be a natural number that is prime (as a typeclass fact) and assume $p \neq 2$. Let $S$ be a finite set of primes, and let $M$ be a representation over $\mathbb{Z}/p$ of the group $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of field automorphisms of an algebraic closure of $\mathbb{Q}$ over $\mathbb{Q}$, assumed finite-dimensional over $\mathbb{Z}/p$. Let $u$ be an element of `Unit`, so that `Sum.inl u` names the archimedean slot of the index type `extArithIndex S` $= \mathrm{Unit} \oplus S$; at that slot the family `extArithLoc S` is the homomorphism `archimedeanLoc`, namely the inclusion of the subgroup `archimedeanDecomposition` of $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ into the whole group. Let $N$ be any $\mathbb{Z}/p$-submodule of the first group cohomology $H^1$ of the restriction of $M$ along this inclusion, i.e. of $M$ viewed as a representation of the archimedean decomposition subgroup. The conclusion is that the $\mathbb{Z}/p$-rank of $N$ is zero.
--
--   This is the vanishing of the degree-one cohomology at the archimedean place for odd residue characteristic, in the form needed for the archimedean term of a Greenberg–Wiles type local–global count: the archimedean decomposition subgroup has order dividing $2$, so for $p$ odd its first cohomology with $\mathbb{Z}/p$-coefficients contributes nothing, and hence neither does any submodule of it. It is used in the construction of cohomology classes with prescribed local restrictions ([`groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two`](thm.html#groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two)), in the nondegenerate pairing statement [`groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two`](thm.html#groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two), and in [`groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc`](thm.html#groupCohomology.greenbergWiles_eq_unramifiedMenu_extArithLoc).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_submodule_res_extArithLoc_archSlot_eq_zero.lean

import Definitions.Def_ExtEndgame_ProductionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.finrank_submodule_res_extArithLoc_archSlot_eq_zero
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M] (u : Unit)
    (N : Submodule (ZMod p) (H1 (Rep.res (extArithLoc S (Sum.inl u)) M))) :
    finrank (ZMod p) N = 0 := by sorry
