-- Prove2me | Theorems.Thm_groupCohomology_exists_restrict_rootsOfUnity_mem_levelCoboundaries2_trivial_of_fixingSubgroup
-- name    : groupCohomology.exists_restrict_rootsOfUnity_mem_levelCoboundaries2_trivial_of_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/be751b7e-bbc8-5502-b8ff-18330721d72e
-- title:
--   Trivial mod-p level 2-cocycles split over an unramified layer
-- statement:
--   Let $p$ be a prime and let $q$ be a prime; write $\overline{\mathbb{Q}}_q$ for `PadicAlgCl q` and $G_q = \mathrm{Aut}_{\mathbb{Q}_q}(\overline{\mathbb{Q}}_q)$ for `primeLocalGaloisGroup q`. Let $K$ be an intermediate field of $\mathbb{Q}_q \subseteq \overline{\mathbb{Q}}_q$ which is finite-dimensional over $\mathbb{Q}_q$ and which contains every $\zeta \in \overline{\mathbb{Q}}_q$ with $\zeta^p = 1$. Let $H \le G_q$ be the fixing subgroup of $K$, and let the level map on $H$ be the inclusion $H \hookrightarrow G_q$ followed by `primeLocalToGlobal q`, the homomorphism sending $\tau$ to the restriction of its underlying $\mathbb{Q}$-algebra automorphism to the algebraic closure of $\mathbb{Q}$ (via `AlgEquiv.restrictNormalHom`). Let $a : H \times H \to \mathbb{Z}/p$ be a function with values in the trivial $H$-representation $\mathbb{Z}/p$ over $\mathbb{Z}/p$, and assume $a$ lies in `levelCocycles₂` for that level map and those trivial coefficients. The conclusion: there is an $N > 0$ such that, setting $T_N$ to be the fixing subgroup of $\mathbb{Q}_q\bigl(\{\zeta : \zeta^{q^N-1}=1\}\bigr)$ inside $G_q$, the restriction of $a$ to $(H \sqcap T_N) \times (H \sqcap T_N)$ along the inclusion $H \sqcap T_N \le H$ lies in `levelCoboundaries₂` for the level map obtained by further composing with this inclusion, again with trivial $\mathbb{Z}/p$ coefficients.
--
--   This is the base case, in the language of subgroups of the local Galois group, of the statement that continuous $H^2$ classes with trivial mod-$p$ coefficients are killed by passing to an unramified layer $K(\mu_{q^N-1})$; the hypothesis $\mu_p \subset K$ makes the coefficient module $\mathbb{Z}/p$ identifiable with $\mu_p$ as an $H$-module. It is obtained from the corresponding $\mu_p$-coefficient splitting statement for $\overline{\mathbb{Q}}_q/K$ together with the two cofinality results comparing fixing subgroups of finite extensions of $K$ with fixing subgroups of number fields under the local-to-global map, and it feeds [`groupCohomology.exists_restrict_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal`](thm.html#groupCohomology.exists_restrict_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_restrict_rootsOfUnity_mem_levelCoboundaries2_trivial_of_fixingSubgroup.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open ExtCitation groupCohomology
open scoped IntermediateField

theorem groupCohomology.exists_restrict_rootsOfUnity_mem_levelCoboundaries2_trivial_of_fixingSubgroup
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ))) [FiniteDimensional ℚ_[(q : ℕ)] K]
    (hμ : ∀ ζ : PadicAlgCl (q : ℕ), ζ ^ p = 1 → ζ ∈ K)
    (a : ↥(((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) × ↥(((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q)))
      → Rep.trivial (ZMod p) ↥(((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) (ZMod p))
    (ha : a ∈ levelCocycles₂ ((primeLocalToGlobal q).comp (((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))).subtype)
      (Rep.trivial (ZMod p) ↥(((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) (ZMod p))) :
    ∃ (N : ℕ) (_ : 0 < N),
      (fun g : ↥((((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) ⊓ (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q)))
            × ↥((((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) ⊓ (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) =>
          a (Subgroup.inclusion inf_le_left g.1, Subgroup.inclusion inf_le_left g.2))
        ∈ levelCoboundaries₂
            (((primeLocalToGlobal q).comp (((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))).subtype).comp
              (Subgroup.inclusion (inf_le_left : (((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) ⊓ (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q)) ≤ (((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))))))
            (Rep.trivial (ZMod p) ↥((((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) ⊓ (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) (ZMod p)) := by sorry
