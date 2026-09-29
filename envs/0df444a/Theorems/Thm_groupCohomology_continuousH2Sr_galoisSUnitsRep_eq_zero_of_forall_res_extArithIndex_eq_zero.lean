-- Prove2me | Theorems.Thm_groupCohomology_continuousH2Sr_galoisSUnitsRep_eq_zero_of_forall_res_extArithIndex_eq_zero
-- name    : groupCohomology.continuousH2Sr_galoisSUnitsRep_eq_zero_of_forall_res_extArithIndex_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/10c9aa04-4555-54df-be5f-3065715b42fa
-- title:
--   Hasse principle for p-torsion of H²(Γ_F,mathcal O_S^×)
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes with $p\in S$ (as the element `pPrime p`). Let $F$ be an intermediate field of $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ` over $\mathbb Q$ which is Galois over $\mathbb Q$ and satisfies `IsUnramifiedOutside S`, i.e. $F/\mathbb Q$ is finite and for every prime $q\notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ in the nonunits of $A$, the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ over $\mathbb Q$ lies in the fixing subgroup $\Gamma_F=$ `F.fixingSubgroup`. For each $v$ in `extArithIndex S` $=\mathrm{Unit}\sqcup S$ let `extArithLoc S v` be the inclusion of the archimedean decomposition subgroup (for the $\mathrm{Unit}$ index) resp. the map `primeLocalToGlobal q` from the local Galois group at $q$ (for $v=q\in S$); let $\gamma$ assign to each $v$ and each coset $t$ in $\Gamma\big/\big(\Gamma_F\sqcup\operatorname{range}(\mathtt{extArithLoc}\,S\,v)\big)$ an element $\gamma_{v,t}$ of $\Gamma$, with $\gamma_{v,t}$ mapping to $t$. Let $x$ be an element of `continuousH2Sr` for the inclusion $\Gamma_F\to\Gamma$, the set $S$, and the restriction to $\Gamma_F$ of the $\mathbb Z$-representation `galoisSUnitsRep S` of $\Gamma$ on the group `galoisSUnits S` of units $u$ of $\overline{\mathbb Q}$ such that $u$ and $u^{-1}$ lie in every valuation subring lying over no prime of $S$; thus $x$ is a class of `levelCocyclesSr₂` modulo `levelCoboundariesSr₂`. Assume $p\cdot x=0$, and assume that for every $v$ and every coset $t$ the class of $x$ in `continuousH2` (via `continuousH2SrToContinuousH2`) is carried to $0$ by `continuousH2Map` along the inclusion $\Gamma_F\cap\gamma_{v,t}\,\operatorname{range}(\mathtt{extArithLoc}\,S\,v)\,\gamma_{v,t}^{-1}\to\Gamma_F$ and the coefficient map `galoisSUnitsToUnits S` into `Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)`. Then $x=0$.
--
--   This is the injectivity (Hasse principle) statement for the $p$-torsion of the second cohomology of $\mathrm{Gal}(\overline{\mathbb Q}/F)$ with $S$-unit coefficients: a $p$-torsion class whose restriction to the decomposition group of every place of $F$ above $S\cup\{\infty\}$ vanishes in the cohomology of the full unit group is zero. It is used in the construction of classes with prescribed local behaviour, via [`groupCohomology.exists_forall_eq_res_continuousH2Sr_galoisSUnitsRep_add_zsmul_of_sq_eq_neg_one`](thm.html#groupCohomology.exists_forall_eq_res_continuousH2Sr_galoisSUnitsRep_add_zsmul_of_sq_eq_neg_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_continuousH2Sr_galoisSUnitsRep_eq_zero_of_forall_res_extArithIndex_eq_zero.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_GaloisSUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.continuousH2Sr_galoisSUnitsRep_eq_zero_of_forall_res_extArithIndex_eq_zero
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ F] (hF : F.IsUnramifiedOutside S)
    (γ : ∀ v : extArithIndex S, (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S v).range) →
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hγ : ∀ v t, (γ v t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S v).range)) = t)
    (x : continuousH2Sr F.fixingSubgroup.subtype S (Rep.res F.fixingSubgroup.subtype (galoisSUnitsRep S)))
    (hx : (p : ℤ) • x = 0)
    (h : ∀ (v : extArithIndex S) (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S v).range)),
      continuousH2Map (rH := F.fixingSubgroup.subtype)
          (rG := (F.fixingSubgroup ⊓ ((extArithLoc S v).range.map (MulAut.conj (γ v t)).toMonoidHom)).subtype)
          (A := Rep.res F.fixingSubgroup.subtype (galoisSUnitsRep S))
          (B := Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S v).range.map (MulAut.conj (γ v t)).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))
          (Subgroup.inclusion inf_le_left) (fun _ => rfl) (galoisSUnitsToUnits S) (fun _ _ => rfl)
          (continuousH2SrToContinuousH2 F.fixingSubgroup.subtype S (Rep.res F.fixingSubgroup.subtype (galoisSUnitsRep S)) x) = 0) :
    x = 0 := by sorry
