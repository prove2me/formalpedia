-- Prove2me | Theorems.Thm_groupCohomology_natCard_torsionBy_continuousH2_inf_map_conj_range_primeLocalToGlobal_le
-- name    : groupCohomology.natCard_torsionBy_continuousH2_inf_map_conj_range_primeLocalToGlobal_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/53bdff4a-9b96-58a0-a19b-af13d9a12dee
-- title:
--   At most p elements in p-torsion of local H²
-- statement:
--   Fix a prime $p$ and a prime $q$, a subfield $F$ of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` that is finite-dimensional over $\mathbb Q$, and an element $g$ of $\Gamma = \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$. Let $K_q \le \Gamma$ be the range of `primeLocalToGlobal q`, the homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}_q/\mathbb Q_q)$ (the automorphism group of `PadicAlgCl q` over $\mathbb Q_p$ for $p=q$) to $\Gamma$ obtained by restricting scalars to $\mathbb Q$ and then restricting along `AlgEquiv.restrictNormalHom` to $\overline{\mathbb Q}$, and let $D$ be the intersection of the fixing subgroup $\Gamma_F$ of $F$ with the image $gK_qg^{-1}$ of $K_q$ under conjugation by $g$. Consider the $\mathbb Z$-module `continuousH2` formed from the inclusion $D \hookrightarrow \Gamma$ as level-homomorphism and from the restriction to $D$ of the $\Gamma$-representation `Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)` on the units $\overline{\mathbb Q}^{\times}$, namely the quotient of the submodule `levelCocycles₂` of $2$-cocycles of finite level by the pullback to it of `levelCoboundaries₂`. The assertion is that the $p$-torsion submodule `Submodule.torsionBy ℤ _ (p : ℤ)` of this module is finite and has at most $p$ elements.
--
--   This is the local input of the counting arguments: the module in question is the Brauer group of the decomposition field of the place of $F$ determined by $g$ and $q$, whose $p$-torsion is in fact cyclic of order exactly $p$, only the upper bound being recorded. It is used in the bound [`groupCohomology.finprod_natCard_torsionBy_continuousH2_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one`](thm.html#groupCohomology.finprod_natCard_torsionBy_continuousH2_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one), one factor for each finite place, and the proof passes through the identification over a $p$-adic base field together with Kummer theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_natCard_torsionBy_continuousH2_inf_map_conj_range_primeLocalToGlobal_le.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology ExtCitation

theorem groupCohomology.natCard_torsionBy_continuousH2_inf_map_conj_range_primeLocalToGlobal_le
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Finite ↥(Submodule.torsionBy ℤ
        (continuousH2 (F.fixingSubgroup ⊓ ((primeLocalToGlobal q).range.map (MulAut.conj g).toMonoidHom)).subtype
          (Rep.res (F.fixingSubgroup ⊓ ((primeLocalToGlobal q).range.map (MulAut.conj g).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ)) ∧
    Nat.card ↥(Submodule.torsionBy ℤ
        (continuousH2 (F.fixingSubgroup ⊓ ((primeLocalToGlobal q).range.map (MulAut.conj g).toMonoidHom)).subtype
          (Rep.res (F.fixingSubgroup ⊓ ((primeLocalToGlobal q).range.map (MulAut.conj g).toMonoidHom)).subtype
            (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) (p : ℤ)) ≤ p := by sorry
