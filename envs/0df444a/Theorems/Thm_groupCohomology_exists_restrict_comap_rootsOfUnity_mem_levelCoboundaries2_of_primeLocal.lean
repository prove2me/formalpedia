-- Prove2me | Theorems.Thm_groupCohomology_exists_restrict_comap_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal
-- name    : groupCohomology.exists_restrict_comap_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/094c2071-63c4-5ed8-95f4-bc69d682e094
-- title:
--   Level 2-cocycles become coboundaries on an unramified subgroup
-- statement:
--   Fix a prime $p$ and a prime $q$, and write $G_q = \mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$ for `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_q$-algebra automorphisms of `PadicAlgCl q`, together with the homomorphism `primeLocalToGlobal q` to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to the algebraic closure of $\mathbb{Q}$ inside `PadicAlgCl q`. Let $S \le G_q$ be a subgroup such that for some intermediate field $F_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ finite over $\mathbb{Q}$ the preimage under `primeLocalToGlobal q` of the fixing subgroup of $F_0$ is contained in $S$, and let $B$ be a finite-dimensional representation of $S$ over $\mathbb{Z}/p$ which is smooth in the sense that every $b \in B$ is fixed by all $s \in S$ whose image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ lies in the fixing subgroup of some intermediate field $F$ finite over $\mathbb{Q}$ (the field depending on $b$). Let $b : S \times S \to B$ lie in `levelCocycles₂` for the level map $S \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ given by `primeLocalToGlobal q` composed with the inclusion of $S$, with coefficients $B$. Then there is an $N > 0$ such that, setting $T_N \le G_q$ to be the fixing subgroup of $\mathbb{Q}_q\bigl(\{\zeta \in \,$`PadicAlgCl q`$\ :\ \zeta^{q^N-1}=1\}\bigr)$ and $U_N =$ the preimage of $T_N$ in $S$ (`Subgroup.comap S.subtype`), the function $U_N \times U_N \to B$ obtained from $b$ by composing with the inclusion $U_N \hookrightarrow S$ in both arguments lies in `levelCoboundaries₂` for the level map on $U_N$ induced by the above and for the restriction `Rep.res` of $B$ to $U_N$.
--
--   This is the statement that a level (continuous) $2$-cocycle of a smooth finite $\mathbb{Z}/p$-representation of an open subgroup $S$ of a local Galois group at $q$ becomes a coboundary after restriction to the subgroup cutting out a finite unramified layer, here phrased with the unramified subgroup realised as a subgroup $U_N$ of $S$ rather than as $S \cap T_N$ inside $G_q$. That shape is the one consumed by the coinduction (Shapiro) step for $U_N \le S$ in the construction of the local deformation data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_restrict_comap_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal.lean

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

theorem groupCohomology.exists_restrict_comap_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (B : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) B]
    (hsm : ∀ b : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s b = b)
    (b : S × S → B) (hb : b ∈ levelCocycles₂ ((primeLocalToGlobal q).comp S.subtype) B) :
    ∃ (N : ℕ) (_ : 0 < N),
      (fun g : ↥(Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q)))
            × ↥(Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))) =>
          b ((Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).subtype g.1,
             (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).subtype g.2))
        ∈ levelCoboundaries₂
            (((primeLocalToGlobal q).comp S.subtype).comp (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).subtype)
            (Rep.res (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).subtype B) := by sorry
