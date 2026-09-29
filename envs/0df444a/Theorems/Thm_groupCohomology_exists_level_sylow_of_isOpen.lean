-- Prove2me | Theorems.Thm_groupCohomology_exists_level_sylow_of_isOpen
-- name    : groupCohomology.exists_level_sylow_of_isOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/5d95df28-2981-534f-9e8c-274fc6556e97
-- title:
--   A Sylow p-level inside an open subgroup of G_{ℚ_q}
-- statement:
--   Fix a prime $p$ and a prime $q$, and write $G_q$ for `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_q$-algebra automorphisms of the chosen algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$, together with the homomorphism `primeLocalToGlobal q` $: G_q \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to the normal subextension $\overline{\mathbb{Q}}$. Let $S \le G_q$ be a subgroup which contains the preimage under `primeLocalToGlobal q` of the fixing subgroup of some intermediate field $F_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ finite over $\mathbb{Q}$, and let $M$ be a representation of $S$ over $\mathbb{Z}/p$, finite-dimensional over $\mathbb{Z}/p$, which is smooth in the sense that every $m \in M$ is fixed by all $s \in S$ whose image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixes some finite extension $F$ of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ depending on $m$. The conclusion produces subgroups $U, T \le G_q$ such that: $T \le S$; $T$ contains the preimage of the fixing subgroup of some finite extension of $\mathbb{Q}$ in $\overline{\mathbb{Q}}$; $T$ viewed as a subgroup of $S$ has finite index whose image in $\mathbb{Z}/p$ is a unit, i.e. the index is prime to $p$; each $s \in T$ has $s^{p^n} \in U$ for some $n$; each $s \in S$ lying in $U$ acts trivially on $M$; and `cycloChar p` takes the value $1$ on the image under `primeLocalToGlobal q` of every $u \in U$. No normality of $U$, nor containment of $U$ in $S$, is asserted.
--
--   This is the construction of a "Sylow $p$-level" inside an open subgroup of a local Galois group: an open subgroup $T$ of index prime to $p$ which is pro-$p$ modulo a deep level $U$ acting trivially both on the given smooth mod $p$ representation and on the mod $p$ cyclotomic line. It is used by [`groupCohomology.bijective_theta_dualTwist_of_isOpen`](thm.html#groupCohomology.bijective_theta_dualTwist_of_isOpen) to reduce a local duality statement over $S$ to the situation where the relevant group acts unipotently.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_level_sylow_of_isOpen.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_level_sylow_of_isOpen
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (M : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → M.ρ s m = m) :
    ∃ (U T : Subgroup (primeLocalGaloisGroup q)),
      T ≤ S ∧
      (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
        F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ T) ∧
      (T.subgroupOf S).FiniteIndex ∧ IsUnit (((T.subgroupOf S).index : ℕ) : ZMod p) ∧
      (∀ s : primeLocalGaloisGroup q, s ∈ T → ∃ n : ℕ, s ^ (p ^ n) ∈ U) ∧
      (∀ s : S, (s : primeLocalGaloisGroup q) ∈ U → ∀ m : M, M.ρ s m = m) ∧
      (∀ u : primeLocalGaloisGroup q, u ∈ U → (cycloChar p) (primeLocalToGlobal q u) = 1) := by sorry
