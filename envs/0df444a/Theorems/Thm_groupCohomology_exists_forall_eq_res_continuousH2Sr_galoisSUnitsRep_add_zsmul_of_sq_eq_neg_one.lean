-- Prove2me | Theorems.Thm_groupCohomology_exists_forall_eq_res_continuousH2Sr_galoisSUnitsRep_add_zsmul_of_sq_eq_neg_one
-- name    : groupCohomology.exists_forall_eq_res_continuousH2Sr_galoisSUnitsRep_add_zsmul_of_sq_eq_neg_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/08611d29-2fae-542a-bc80-f63cbd1bb52c
-- title:
--   Corank at most one for S-localisation of H²(Γ_F,mathcal O_S^×)[p]
-- statement:
--   Let $p$ be a prime, $S$ a finite set of rational primes containing $p$ (as the element `pPrime p`), and let $F$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ that is Galois over $\mathbb Q$ and satisfies `IsUnramifiedOutside S`, i.e. $F/\mathbb Q$ is finite and for every prime $q\notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$, the image in $\Gamma=\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ lies in $\Gamma_F=$ `F.fixingSubgroup`; assume moreover that if $p=2$ then $F$ contains an element $i$ with $i^2=-1$. For each $q\in S$ let $K_q\le\Gamma$ be the range of `extArithLoc S (Sum.inr q)`, the map of the local Galois group at $q$ into $\Gamma$, and let $\gamma$ assign to each $q$ and each class $t\in\Gamma/(\Gamma_F\sqcup K_q)$ an element $\gamma_{q,t}\in\Gamma$ lifting $t$ (hypothesis $h\gamma$). Put $D_{q,t}=\Gamma_F\cap\gamma_{q,t}K_q\gamma_{q,t}^{-1}$ and write $H^2(D_{q,t})$ for `continuousH2` of the inclusion $D_{q,t}\hookrightarrow\Gamma$ with coefficients in the restriction to $D_{q,t}$ of the $\Gamma$-module $\overline{\mathbb Q}^\times$ (`Rep.ofAlgebraAutOnUnits`), that is, the quotient of the module of level cocycles `levelCocycles₂` by those that are level coboundaries. The assertion is that there exists a family $w_{q,t}\in H^2(D_{q,t})$ with $p\cdot w_{q,t}=0$ for all $q,t$ such that every family $y_{q,t}\in H^2(D_{q,t})$ with $p\cdot y_{q,t}=0$ for all $q,t$ is of the form $y_{q,t}=\mathrm{res}_{D_{q,t}}(x)+c\cdot w_{q,t}$ for some integer $c$ and some $x$ in `continuousH2Sr` of $\Gamma_F\hookrightarrow\Gamma$ with coefficients in the restriction to $\Gamma_F$ of the $\Gamma$-module `galoisSUnitsRep S` of $S$-units of $\overline{\mathbb Q}$ (units $u$ such that $u$ and $u^{-1}$ lie in every valuation subring lying over no prime of $S$) satisfying $p\cdot x=0$; here $\mathrm{res}_{D_{q,t}}$ denotes the map `continuousH2SrToContinuousH2` followed by `continuousH2Map` along the inclusion $D_{q,t}\le\Gamma_F$ and the coefficient map `galoisSUnitsToUnits` from $S$-units into $\overline{\mathbb Q}^\times$.
--
--   This is the existence, or surjectivity-up-to-corank-one, half of the Hasse–Brauer–Noether/Tate localisation sequence for $H^2(\Gamma_F,\mathcal O_S^\times)[p]$: the $p$-torsion of the local $H^2$'s at the places of $F$ above $S$ is exhausted by global $S$-unit classes together with a single fixed family $w$, in the edition where $F$ is assumed to contain $\sqrt{-1}$ when $p=2$. Together with the injectivity statement [`groupCohomology.continuousH2Sr_galoisSUnitsRep_eq_zero_of_forall_res_extArithIndex_eq_zero`](thm.html#groupCohomology.continuousH2Sr_galoisSUnitsRep_eq_zero_of_forall_res_extArithIndex_eq_zero) and the counting bound [`groupCohomology.finprod_natCard_torsionBy_continuousH2_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one`](thm.html#groupCohomology.finprod_natCard_torsionBy_continuousH2_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one), it feeds the version with trivial-coefficient normalisation, [`groupCohomology.exists_forall_eq_res_continuousH2Sr_trivial_add_smul_of_exists_sq_eq_neg_one`](thm.html#groupCohomology.exists_forall_eq_res_continuousH2Sr_trivial_add_smul_of_exists_sq_eq_neg_one), used in the global Galois-cohomological input to the deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_forall_eq_res_continuousH2Sr_galoisSUnitsRep_add_zsmul_of_sq_eq_neg_one.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_GaloisSUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_forall_eq_res_continuousH2Sr_galoisSUnitsRep_add_zsmul_of_sq_eq_neg_one
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ F] (hF : F.IsUnramifiedOutside S)
    (h4 : p = 2 → ∃ i ∈ F, i ^ 2 = -1)
    (γ : ∀ q : ↥S, (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range) →
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hγ : ∀ q t, (γ q t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range)) = t) :
    ∃ w : ∀ (q : ↥S) (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range)),
        continuousH2 (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ q t)).toMonoidHom)).subtype
          (Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ q t)).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))),
      (∀ q t, (p : ℤ) • w q t = 0) ∧
      ∀ y : ∀ (q : ↥S) (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range)),
          continuousH2 (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ q t)).toMonoidHom)).subtype
            (Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ q t)).toMonoidHom)).subtype
              (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))),
        (∀ q t, (p : ℤ) • y q t = 0) →
        ∃ (x : continuousH2Sr F.fixingSubgroup.subtype S (Rep.res F.fixingSubgroup.subtype (galoisSUnitsRep S))) (c : ℤ),
          (p : ℤ) • x = 0 ∧
          ∀ q t, y q t =
            continuousH2Map (rH := F.fixingSubgroup.subtype)
                (rG := (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ q t)).toMonoidHom)).subtype)
                (A := Rep.res F.fixingSubgroup.subtype (galoisSUnitsRep S))
                (B := Rep.res (F.fixingSubgroup ⊓ ((extArithLoc S (Sum.inr q)).range.map (MulAut.conj (γ q t)).toMonoidHom)).subtype
                  (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))
                (Subgroup.inclusion inf_le_left) (fun _ => rfl) (galoisSUnitsToUnits S) (fun _ _ => rfl)
                (continuousH2SrToContinuousH2 F.fixingSubgroup.subtype S (Rep.res F.fixingSubgroup.subtype (galoisSUnitsRep S)) x)
              + c • w q t := by sorry
