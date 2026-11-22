-- Prove2me | solution 1 for Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeight_headMargins_of_linearBounds
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:02:01.92325+00:00
-- url     : https://prove2.me/submissions/61d3f6ba-ddda-488f-9d7b-c2e7e43117cf

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_010

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightHeadMarginAlgebra -/
section


/-!
# Finite head-margin algebra for the post-height target

This file isolates the elementary finite-dimensional argument behind the
head-simplex margins.  It contains no realization, certificate, source-state,
or placement hypothesis.

For fixed positive coordinate scales `a p` and nonnegative upper scales
`b p`, suppose a target coordinate lies between `a p * N` and `b p * N`,
while its active mass lies between `cLower * N` and `cUpper * N`.  A finite
minimum of the `a p` gives a common positive vertex reserve.  If the exponent
is large enough that

`2 * sum_p b p <= E * cLower`,

then the zero vertex has reserve at least `1 / 2`.  The minimum of these two
reserves works simultaneously for any two target/mass pairs satisfying the
same envelopes, in particular for the frozen source mass and the fresh
post-height mass.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Fixed finite coordinate and simplex margins -/



/-- The finite coordinate floor is positive when every displayed coordinate
scale is positive. -/
theorem bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor_pos
    {P : Finset Nat} (a : {p : Nat // p ∈ P} → Real)
    (ha : ∀ p, 0 < a p) :
    0 < bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a := by
  classical
  unfold bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor
  have hmem :=
    Finset.min'_mem
      (insert 1
        ((Finset.univ : Finset {p : Nat // p ∈ P}).image a))
      (Finset.insert_nonempty 1 _)
  rcases Finset.mem_insert.mp hmem with hOne | hcoordinate
  · rw [hOne]
    norm_num
  · obtain ⟨p, _hp, hp⟩ := Finset.mem_image.mp hcoordinate
    rw [← hp]
    exact ha p

/-- The finite coordinate floor lies below every coordinate scale. -/
theorem bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor_le
    {P : Finset Nat} (a : {p : Nat // p ∈ P} → Real)
    (p : {p : Nat // p ∈ P}) :
    bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a ≤ a p := by
  classical
  unfold bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor
  exact
    Finset.min'_le _ _
      (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_image.mpr
          ⟨p, Finset.mem_univ p, rfl⟩)))



/-- The common head-simplex margin is strictly positive. -/
theorem bankPaperCanonicalSectionNinePostHeightHeadMargin_pos
    {P : Finset Nat} (E : Nat)
    (a : {p : Nat // p ∈ P} → Real) (cUpper : Real)
    (hE : 0 < E) (ha : ∀ p, 0 < a p) (hcUpper : 0 < cUpper) :
    0 < bankPaperCanonicalSectionNinePostHeightHeadMargin E a cUpper := by
  unfold bankPaperCanonicalSectionNinePostHeightHeadMargin
  apply lt_min
  · norm_num
  · exact div_pos
      (bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor_pos a ha)
      (mul_pos (by exact_mod_cast hE) hcUpper)

/-! ## Choosing a sufficiently large exponent -/



/-! ## One target/mass pair -/

/-- Linear coordinate and mass envelopes imply uniform positive vertex and
zero-vertex margins for one head target.

The exponent condition is completely explicit.  The resulting margin depends
only on the fixed finite lower envelope, `E`, and `cUpper`, not on `N`, the
target, or the active mass. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_headMargins_of_linearBounds
    {P : Finset Nat}
    (E : Nat) (hE : 0 < E)
    (a b : {p : Nat // p ∈ P} → Real)
    (cLower cUpper N q : Real)
    (target : {p : Nat // p ∈ P} → Real)
    (ha : ∀ p, 0 < a p)
    (hb : ∀ p, 0 ≤ b p)
    (hcLower : 0 < cLower) (hcUpper : 0 < cUpper)
    (hN : 0 < N) (hq : 0 < q)
    (htargetLower : ∀ p, a p * N ≤ target p)
    (htargetUpper : ∀ p, target p ≤ b p * N)
    (hqLower : cLower * N ≤ q)
    (hqUpper : q ≤ cUpper * N)
    (hElarge :
      2 * (∑ p : {p : Nat // p ∈ P}, b p) ≤
        (E : Real) * cLower) :
    let margin :=
      bankPaperCanonicalSectionNinePostHeightHeadMargin E a cUpper
    0 < margin ∧
      (∀ p, margin ≤ target p / ((E : Real) * q)) ∧
      margin ≤
        1 - ∑ p : {p : Nat // p ∈ P},
          target p / ((E : Real) * q) := by
  dsimp only
  have hEReal : 0 < (E : Real) := by
    exact_mod_cast hE
  have hEq : 0 < (E : Real) * q :=
    mul_pos hEReal hq
  have hEcLower : 0 < (E : Real) * cLower :=
    mul_pos hEReal hcLower
  have hEcUpper : 0 < (E : Real) * cUpper :=
    mul_pos hEReal hcUpper
  have hmarginPos :
      0 <
        bankPaperCanonicalSectionNinePostHeightHeadMargin
          E a cUpper :=
    bankPaperCanonicalSectionNinePostHeightHeadMargin_pos
      E a cUpper hE ha hcUpper
  refine ⟨hmarginPos, ?_, ?_⟩
  · intro p
    apply le_trans (min_le_right _ _)
    apply (div_le_div_iff₀ hEcUpper hEq).2
    have hfloorTarget :
        bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a * N ≤
          target p := by
      exact
        (mul_le_mul_of_nonneg_right
          (bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor_le a p)
          hN.le).trans (htargetLower p)
    calc
      bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a *
            ((E : Real) * q) =
          ((E : Real) *
              bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a) *
            q := by
        ring
      _ ≤
          ((E : Real) *
              bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a) *
            (cUpper * N) := by
        apply mul_le_mul_of_nonneg_left hqUpper
        exact
          mul_nonneg hEReal.le
            (bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor_pos
              a ha).le
      _ =
          (bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a * N) *
            ((E : Real) * cUpper) := by
        ring
      _ ≤ target p * ((E : Real) * cUpper) :=
        mul_le_mul_of_nonneg_right hfloorTarget hEcUpper.le
  · have htermUpper : ∀ p : {p : Nat // p ∈ P},
        target p / ((E : Real) * q) ≤
          b p / ((E : Real) * cLower) := by
      intro p
      apply (div_le_div_iff₀ hEq hEcLower).2
      calc
        target p * ((E : Real) * cLower) ≤
            (b p * N) * ((E : Real) * cLower) :=
          mul_le_mul_of_nonneg_right (htargetUpper p) hEcLower.le
        _ = ((E : Real) * b p) * (cLower * N) := by
          ring
        _ ≤ ((E : Real) * b p) * q := by
          exact
            mul_le_mul_of_nonneg_left hqLower
              (mul_nonneg hEReal.le (hb p))
        _ = b p * ((E : Real) * q) := by
          ring
    have hsumUpper :
        (∑ p : {p : Nat // p ∈ P},
            target p / ((E : Real) * q)) ≤
          ∑ p : {p : Nat // p ∈ P},
            b p / ((E : Real) * cLower) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact htermUpper p
    have hbRatio :
        (∑ p : {p : Nat // p ∈ P}, b p) /
              ((E : Real) * cLower) ≤
          1 / 2 := by
      apply (div_le_iff₀ hEcLower).2
      nlinarith [hElarge]
    have hsumHalf :
        (∑ p : {p : Nat // p ∈ P},
            target p / ((E : Real) * q)) ≤
          1 / 2 := by
      calc
        (∑ p : {p : Nat // p ∈ P},
            target p / ((E : Real) * q)) ≤
            ∑ p : {p : Nat // p ∈ P},
              b p / ((E : Real) * cLower) :=
          hsumUpper
        _ =
            (∑ p : {p : Nat // p ∈ P}, b p) /
              ((E : Real) * cLower) := by
          rw [Finset.sum_div]
        _ ≤ 1 / 2 := hbRatio
    apply le_trans (min_le_left _ _)
    linarith

/-! ## Simultaneous source and post-height margins -/



end

end Erdos390.WholePaper

end

theorem solution :
∀ {P : Finset.{0} Nat} (E : Nat),
  LT.lt.{0} (0 : Nat) E →
    ∀ (a b : ↥P → Real) (cLower cUpper N q : Real) (target : ↥P → Real),
      (∀ (p : ↥P), LT.lt.{0} (0 : Real) (a p)) →
        (∀ (p : ↥P), LE.le.{0} (0 : Real) (b p)) →
          LT.lt.{0} (0 : Real) cLower →
            LT.lt.{0} (0 : Real) cUpper →
              LT.lt.{0} (0 : Real) N →
                LT.lt.{0} (0 : Real) q →
                  (∀ (p : ↥P), LE.le.{0} (HMul.hMul.{0, 0, 0} (a p) N) (target p)) →
                    (∀ (p : ↥P), LE.le.{0} (target p) (HMul.hMul.{0, 0, 0} (b p) N)) →
                      LE.le.{0} (HMul.hMul.{0, 0, 0} cLower N) q →
                        LE.le.{0} q (HMul.hMul.{0, 0, 0} cUpper N) →
                          LE.le.{0} (HMul.hMul.{0, 0, 0} (2 : Real) (∑ p, b p)) (HMul.hMul.{0, 0, 0} (↑E) cLower) →
                            have margin :=
                              Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightHeadMargin E a cUpper;
                            And (LT.lt.{0} (0 : Real) margin)
                              (And
                                (∀ (p : ↥P),
                                  LE.le.{0} margin (HDiv.hDiv.{0, 0, 0} (target p) (HMul.hMul.{0, 0, 0} (↑E) q)))
                                (LE.le.{0} margin
                                  (HSub.hSub.{0, 0, 0} (1 : Real)
                                    (∑ p, HDiv.hDiv.{0, 0, 0} (target p) (HMul.hMul.{0, 0, 0} (↑E) q))))) := by
  exact @Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeight_headMargins_of_linearBounds
