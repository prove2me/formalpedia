-- Prove2me | Theorems.Thm_groupCohomology_pow_natCard_places_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one
-- name    : groupCohomology.pow_natCard_places_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/d29b6acc-743b-5a3b-b235-041a7c6e6f23
-- title:
--   Lower bound for p-torsion in H²(G_{F,S},𝒪_S^×)
-- statement:
--   Let $p$ be a prime, let $S$ be a finite set of rational primes with $p \in S$, and let $\Gamma = \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ act on $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Let $F$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is Galois over $\mathbb{Q}$ and satisfies `IsUnramifiedOutside S`, i.e. $F$ is finite over $\mathbb{Q}$ and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the inertia subgroup of $A$ over $\mathbb{Q}$, pushed into $\Gamma$, lies in $\Gamma_F =$ `F.fixingSubgroup`; assume moreover that if $p = 2$ then $F$ contains an element $i$ with $i^2 = -1$. Write $M$ for the $p$-torsion submodule of `continuousH2Sr` for the inclusion $\Gamma_F \hookrightarrow \Gamma$, the set $S$ and the restriction to $\Gamma_F$ of the $\mathbb{Z}$-representation `galoisSUnitsRep S` on the group of $x \in \overline{\mathbb{Q}}^\times$ with $x, x^{-1}$ integral at every valuation subring lying over no prime of $S$; this `continuousH2Sr` is the quotient of `levelCocyclesSr₂` by the coboundaries inside it. The assertion is threefold: $M$ is finite; $p^{n_S} \le p\,|M|$, where $n_S = \sum_{q \in S} |\Gamma/(\Gamma_F \sqcup \mathrm{im}\,\mathrm{Gal}(\overline{\mathbb{Q}_q}/\mathbb{Q}_q))|$; and, if $p = 2$ and [`complexConjugation`](def/GaloisRep_ComplexConjugation.html#L30) lies in $\Gamma_F$, then $p^{n_S + n_\infty} \le p\,|M|$, where $n_\infty = |\Gamma/(\Gamma_F \sqcup \mathrm{archimedeanDecomposition})|$.
--
--   The counting form of the existence half of the Albert–Brauer–Hasse–Noether theorem for the $p$-torsion of the Brauer group of the ring of $S$-integers of $F$: each place of $F$ above $S$ (and each real place, when $p = 2$) contributes a local invariant, the sum of the invariants being the only relation. It feeds the global bound [`groupCohomology.finprod_natCard_torsionBy_continuousH2_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one`](thm.html#groupCohomology.finprod_natCard_torsionBy_continuousH2_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one), used in controlling $S$-ramified deformation problems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_pow_natCard_places_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_GaloisSUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.pow_natCard_places_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ F] (hF : F.IsUnramifiedOutside S)
    (h4 : p = 2 → ∃ i ∈ F, i ^ 2 = -1) :
    Finite ↥(Submodule.torsionBy ℤ
        (continuousH2Sr F.fixingSubgroup.subtype S (Rep.res F.fixingSubgroup.subtype (galoisSUnitsRep S))) (p : ℤ)) ∧
    p ^ (∑ q : ↥S, Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸
            (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range)))
      ≤ p * Nat.card ↥(Submodule.torsionBy ℤ
          (continuousH2Sr F.fixingSubgroup.subtype S (Rep.res F.fixingSubgroup.subtype (galoisSUnitsRep S))) (p : ℤ)) ∧
    (p = 2 → complexConjugation ∈ F.fixingSubgroup →
      p ^ ((∑ q : ↥S, Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸
              (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inr q)).range))) +
            Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (F.fixingSubgroup ⊔ (extArithLoc S (Sum.inl ())).range)))
        ≤ p * Nat.card ↥(Submodule.torsionBy ℤ
          (continuousH2Sr F.fixingSubgroup.subtype S (Rep.res F.fixingSubgroup.subtype (galoisSUnitsRep S))) (p : ℤ))) := by sorry
