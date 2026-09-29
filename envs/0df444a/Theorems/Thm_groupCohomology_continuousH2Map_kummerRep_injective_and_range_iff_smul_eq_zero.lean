-- Prove2me | Theorems.Thm_groupCohomology_continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero
-- name    : groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/56955070-38f7-5365-8866-7e3504ac89f1
-- title:
--   Continuous Kummer map H²(G_K,μₚ)→ H²(G_K,Ω^×): injective with p-torsion image
-- statement:
--   Let $K\subseteq\Omega$ be fields with $\Omega$ a Galois, algebraically closed extension of $K$, let $p$ be a prime, and let $r\colon(\Omega\simeq_K\Omega)\to(\overline{\mathbb{Q}}\simeq_{\mathbb{Q}}\overline{\mathbb{Q}})$ be a homomorphism of automorphism groups (a "level map", where $\overline{\mathbb{Q}}$ is `AlgebraicClosure ℚ`). Two cofinality hypotheses are assumed: `hlevel`, that for every intermediate field $E$ of $\Omega/K$ finite over $K$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ finite over $\mathbb{Q}$ with $r^{-1}(\mathrm{Gal}(\overline{\mathbb{Q}}/F))$ contained in the fixing subgroup of $E$; and `hopen`, the converse cofinality, that every such $F$ admits such an $E$ whose fixing subgroup maps into the fixing subgroup of $F$. Write $\mathrm{continuousH2}\,r\,M$ for the quotient of the level-$2$ cocycles `levelCocycles₂ r M` by the level-$2$ coboundaries. Let $j$ be the $\mathbb{Z}$-linear map `continuousH2Map` from $\mathrm{continuousH2}$ of the Kummer representation `Kummer.kummerRep K Ω p` — the $(\Omega\simeq_K\Omega)$-module $\mu_p(\Omega)$ of $p$-th roots of unity, written additively — to $\mathrm{continuousH2}$ of `Rep.ofAlgebraAutOnUnits K Ω`, i.e. of $\Omega^\times$, induced by the identity on the Galois group and the inclusion $\mu_p(\Omega)\hookrightarrow\Omega^\times$. Then $j$ is injective, and an element $x$ of $\mathrm{continuousH2}\,r\,\Omega^\times$ lies in the range of $j$ if and only if $p\cdot x=0$.
--
--   This is Kummer theory in degree two in the continuous (level-wise) setting: the continuous cohomology of $\mu_p$ in degree $2$ embeds into that of $\Omega^\times$, the Brauer group of $K$, with image exactly its $p$-torsion. It underlies the treatment of local invariants and of the $p$-part of the Brauer group used downstream, being cited for the existence and uniqueness of local inverses and for the computation of the continuous $H^2$ of $\mu_p$ in the $p$-adic case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

open groupCohomology IntermediateField

theorem groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup) :
    let j : continuousH2 r (Kummer.kummerRep K Ω p) →ₗ[ℤ] continuousH2 r (Rep.ofAlgebraAutOnUnits K Ω) :=
      continuousH2Map (rH := r) (rG := r) (A := Kummer.kummerRep K Ω p) (B := Rep.ofAlgebraAutOnUnits K Ω)
        (MonoidHom.id _) (fun _ => rfl)
        (MonoidHom.toAdditive (rootsOfUnity p Ω).subtype).toIntLinearMap (fun _ _ => rfl)
    Function.Injective j ∧
      ∀ x : continuousH2 r (Rep.ofAlgebraAutOnUnits K Ω), x ∈ LinearMap.range j ↔ (p : ℤ) • x = 0 := by sorry
