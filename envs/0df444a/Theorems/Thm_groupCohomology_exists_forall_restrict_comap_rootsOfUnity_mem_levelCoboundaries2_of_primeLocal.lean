-- Prove2me | Theorems.Thm_groupCohomology_exists_forall_restrict_comap_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal
-- name    : groupCohomology.exists_forall_restrict_comap_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/6cc12a34-2c3f-5210-b592-bbe013f5c86e
-- title:
--   Uniform killing of level 2-cocycles in a higher unramified layer
-- statement:
--   Fix a prime $p$ and a prime $q$, and write $G_q$ for the group `primeLocalGaloisGroup q` of $\mathbb{Q}_p$-algebra automorphisms of the algebraic closure `PadicAlgCl q` of $\mathbb{Q}_{[q]}$ over $\mathbb{Q}_{[q]}$, together with the homomorphism `primeLocalToGlobal q` to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to the normal subextension $\overline{\mathbb{Q}}$. Let $S \le G_q$ be a subgroup which is open in the sense that there is a finite extension $F_0/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ whose fixing subgroup has preimage under `primeLocalToGlobal q` contained in $S$, and let $B$ be a finite-dimensional $\mathbb{Z}/p$-linear representation of $S$ which is smooth in the sense that every $b \in B$ is fixed by all $s \in S$ whose image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ lies in the fixing subgroup of some finite extension $F/\mathbb{Q}$ depending on $b$. For $N \ge 1$ put $U_N := S \cap \mathrm{Gal}\big(\overline{\mathbb{Q}}_{[q]}/\mathbb{Q}_{[q]}(\mu_{q^N-1})\big)$, realised in Lean as the preimage in $S$ of the fixing subgroup of the intermediate field generated over $\mathbb{Q}_{[q]}$ by $\{\zeta : \zeta^{q^N-1} = 1\}$. Then, given $N_0 \ge 1$, there exist $N \ge 1$ with $N_0 \mid N$ and an inclusion $U_N \le U_{N_0}$ such that every $b : U_{N_0} \times U_{N_0} \to B$ lying in `levelCocycles₂` for the composite $U_{N_0} \hookrightarrow S \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and the restriction of $B$ to $U_{N_0}$ has its restriction to $U_N \times U_N$ in `levelCoboundaries₂` for the corresponding level-$N$ data.
--
--   This is the statement that a single unramified layer $\mathbb{Q}_{[q]}(\mu_{q^N-1})$ can be chosen to kill all continuous degree-two classes of a smooth finite $\mathbb{F}_p$-representation at once, in the relative form that starts from a given layer $U_{N_0}$ rather than from $S$ itself. It is used in the proof that the map induced on continuous $H^2$ by a surjection of local coefficient modules is surjective, where the relative form is needed both for the target module and for the kernel module over an intermediate layer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_forall_restrict_comap_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open ExtCitation groupCohomology

theorem groupCohomology.exists_forall_restrict_comap_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (B : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) B]
    (hsm : ∀ b : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s b = b)
    (N₀ : ℕ) (hN₀ : 0 < N₀) :
    ∃ (N : ℕ) (hle : (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))) ≤ (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N₀ - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q)))), 0 < N ∧ N₀ ∣ N ∧
      ∀ (b : ↥(Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N₀ - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))) × ↥(Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N₀ - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))) → B),
        b ∈ levelCocycles₂ (((primeLocalToGlobal q).comp S.subtype).comp (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N₀ - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).subtype) (Rep.res (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N₀ - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).subtype B) →
        (fun g : ↥(Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))) × ↥(Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))) => b (Subgroup.inclusion hle g.1, Subgroup.inclusion hle g.2))
          ∈ levelCoboundaries₂ (((primeLocalToGlobal q).comp S.subtype).comp (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).subtype) (Rep.res (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).subtype B) := by sorry
