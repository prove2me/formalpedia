-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.abs_fourFiveActualReciprocalProductThree_sub_continuum_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:13:13.468048+00:00
-- url     : https://prove2.me/submissions/c1f08c3e-de71-4671-b457-3f36937ca787

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_009

/- Source module: Erdos390.Full.PrimeBandQuadrature -/
section


/-!
# Audited harmonic prime quadrature on moving positive cells

The continuum transfer in Lemma 8.4 uses prime cells whose endpoints are
powers of the smoothness scale.  This file starts the required arithmetic
quadrature from the actual Chebyshev function.  The key identity below has no
Mertens constant: it subtracts Abel summation at two endpoints and isolates
the quantitative PNT remainder exactly.
-/

open scoped BigOperators
open Set
open Filter Topology Asymptotics

noncomputable section

namespace Erdos390.Full.PrimeBandQuadrature

open MeasureTheory
open Erdos390.Full.PrimeSums
open Erdos390.Full.FriableAsymptotic



























/-! ## The first logarithmic moment -/















/-! ## Quantitative PNT remainder -/





















/-! ## Exact alignment with the paper's logarithmic coordinate -/





















theorem fullReciprocalSumUniformConstant_pos :
    0 < fullReciprocalSumUniformConstant :=
  (Classical.choose_spec
    exists_fullReciprocalSum_interval_error_bound).1



theorem fullReciprocalSumUniform_bound
    (A Y : ℕ) (hA : fullReciprocalSumUniformCutoff ≤ A)
    (hAY : A ≤ Y) :
    |fullReciprocalSum Y - fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
      5 * fullReciprocalSumUniformConstant / Real.log (A : ℝ) ^ 3 :=
  (Classical.choose_spec
    (Classical.choose_spec
      exists_fullReciprocalSum_interval_error_bound).2) A Y hA hAY



end Erdos390.Full.PrimeBandQuadrature

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveReciprocalPrimeBV -/
section


/-!
# Reciprocal-prime bounded-variation transfer for the four/five chamber

This file turns the audited two-endpoint Mertens estimate in
`PrimeBandQuadrature` into a finite signed-measure statement that can be
iterated in the ordered-prime mixture.

On every integer cell `(m-1,m]` we subtract the continuum mass

`log(log m) - log(log (m-1))`

from the actual reciprocal-prime atom.  The prefix of this signed cell
measure is exactly the two-endpoint reciprocal-prime discrepancy.  Finite
Abel summation then bounds its pairing with an arbitrary sequence by the
uniform discrepancy times the right-endpoint value plus the sequence's
discrete variation.  No smoothness hypothesis and no new analytic axiom are
used.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature























theorem fourFiveReciprocalBVSafeCutoff_ge_uniformCutoff :
    fullReciprocalSumUniformCutoff <=
      fourFiveReciprocalBVSafeCutoff :=
  le_max_left _ _

theorem fourFiveReciprocalBVSafeCutoff_ge_two :
    2 <= fourFiveReciprocalBVSafeCutoff :=
  le_max_right _ _

/-- Summing the integer atoms through `n` gives the repository's literal
full reciprocal-prime sum. -/
theorem sum_range_fourFiveReciprocalPrimeAtom (n : Nat) :
    (∑ m ∈ Finset.range (n + 1), fourFiveReciprocalPrimeAtom m) =
      fullReciprocalSum n := by
  unfold fourFiveReciprocalPrimeAtom
    Erdos390.Full.PrimeSums.fullReciprocalSum
    Erdos390.Full.PrimeSums.primesUpTo
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨hm, hp⟩
      exact ⟨⟨Nat.zero_le m, by omega⟩, hp⟩
    · rintro ⟨⟨_hm0, hmn⟩, hp⟩
      exact ⟨by omega, hp⟩
  · intro m _hm
    rfl

private theorem sum_range_anchored_eq_sub
    (f : Nat -> Real) {A n : Nat} (hAn : A <= n) :
    (∑ m ∈ Finset.range (n + 1), if A < m then f m else 0) =
      (∑ m ∈ Finset.range (n + 1), f m) -
        ∑ m ∈ Finset.range (A + 1), f m := by
  have hsubset : Finset.range (A + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_mono (by omega)
  have hfilter :
      (Finset.range (n + 1)).filter (fun m => A < m) =
        Finset.range (n + 1) \ Finset.range (A + 1) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
    omega
  rw [← Finset.sum_filter, hfilter]
  exact (eq_sub_iff_add_eq).2 (Finset.sum_sdiff hsubset (f := f))

/-- The anchored actual-prime atoms have the expected two-endpoint mass. -/
theorem sum_range_fourFiveAnchoredReciprocalPrimeAtom
    {A n : Nat} (hAn : A <= n) :
    (∑ m ∈ Finset.range (n + 1),
        fourFiveAnchoredReciprocalPrimeAtom A m) =
      fullReciprocalSum n - fullReciprocalSum A := by
  unfold fourFiveAnchoredReciprocalPrimeAtom
  rw [sum_range_anchored_eq_sub fourFiveReciprocalPrimeAtom hAn,
    sum_range_fourFiveReciprocalPrimeAtom,
    sum_range_fourFiveReciprocalPrimeAtom]

/-- The continuum cell atoms telescope exactly to the log-log increment. -/
theorem sum_range_fourFiveAnchoredLogLogCellAtom
    {A n : Nat} (hAn : A <= n) :
    (∑ m ∈ Finset.range (n + 1),
        fourFiveAnchoredLogLogCellAtom A m) =
      fourFiveLogLogPrimitive n - fourFiveLogLogPrimitive A := by
  induction n with
  | zero =>
      have hA0 : A = 0 := Nat.eq_zero_of_le_zero hAn
      subst A
      simp [fourFiveAnchoredLogLogCellAtom]
  | succ n ih =>
      by_cases hAn' : A <= n
      · rw [Finset.sum_range_succ, ih hAn']
        have hAlt : A < n + 1 := by omega
        simp only [fourFiveAnchoredLogLogCellAtom, if_pos hAlt,
          Nat.add_sub_cancel]
        ring
      · have hAeq : A = n + 1 := by omega
        subst A
        rw [sub_self]
        apply Finset.sum_eq_zero
        intro m hm
        unfold fourFiveAnchoredLogLogCellAtom
        rw [if_neg]
        have hmle : m <= n + 1 := by
          have hm' := Finset.mem_range.mp hm
          omega
        omega

/-- Prefixes of the signed cell measure are exactly the reciprocal-prime
two-endpoint discrepancy. -/
theorem sum_range_fourFiveReciprocalPrimeSignedCell
    {A n : Nat} (hAn : A <= n) :
    (∑ m ∈ Finset.range (n + 1),
        fourFiveReciprocalPrimeSignedCell A m) =
      fourFiveReciprocalPrimeDiscrepancy A n := by
  unfold fourFiveReciprocalPrimeSignedCell
  rw [Finset.sum_sub_distrib,
    sum_range_fourFiveAnchoredReciprocalPrimeAtom hAn,
    sum_range_fourFiveAnchoredLogLogCellAtom hAn]
  rfl



/-- Exact finite Abel identity for a centered prefix measure. -/
theorem fourFiveFiniteBV_by_parts
    (c f : Nat -> Real) {A Y : Nat} (hAY : A < Y)
    (hprefixA : ∑ m ∈ Finset.range (A + 1), c m = 0) :
    (∑ m ∈ Finset.Ioc A Y, f m * c m) =
      f Y * (∑ m ∈ Finset.range (Y + 1), c m) -
        ∑ m ∈ Finset.Ioc A (Y - 1),
          (f (m + 1) - f m) *
            (∑ k ∈ Finset.range (m + 1), c k) := by
  have habel := Finset.sum_Ioc_by_parts f c hAY
  simp only [smul_eq_mul] at habel
  rw [hprefixA, mul_zero, sub_zero] at habel
  exact habel

/-- A uniformly bounded centered prefix measure pairs with every sequence at
most its prefix bound times right-endpoint-plus-variation. -/
theorem abs_sum_Ioc_mul_le_prefixBound_mul_rightDiscreteBVNorm
    (c f : Nat -> Real) {A Y : Nat} {E : Real}
    (hAY : A <= Y) (hE : 0 <= E)
    (hprefixA : ∑ m ∈ Finset.range (A + 1), c m = 0)
    (hprefix : ∀ m ∈ Finset.Icc A Y,
      |(∑ k ∈ Finset.range (m + 1), c k)| <= E) :
    |(∑ m ∈ Finset.Ioc A Y, f m * c m)| <=
      E * fourFiveRightDiscreteBVNorm f A Y := by
  by_cases hEq : A = Y
  · subst Y
    have hvarNonneg : 0 <= fourFiveRightDiscreteBVNorm f A A := by
      unfold fourFiveRightDiscreteBVNorm
      positivity
    simp only [Finset.Ioc_self, Finset.sum_empty, abs_zero]
    exact mul_nonneg hE hvarNonneg
  have hlt : A < Y := lt_of_le_of_ne hAY hEq
  rw [fourFiveFiniteBV_by_parts c f hlt hprefixA]
  calc
    |f Y * (∑ m ∈ Finset.range (Y + 1), c m) -
        ∑ m ∈ Finset.Ioc A (Y - 1),
          (f (m + 1) - f m) *
            (∑ k ∈ Finset.range (m + 1), c k)| <=
      |f Y * (∑ m ∈ Finset.range (Y + 1), c m)| +
        |∑ m ∈ Finset.Ioc A (Y - 1),
          (f (m + 1) - f m) *
            (∑ k ∈ Finset.range (m + 1), c k)| := abs_sub _ _
    _ <= |f Y| * E +
        ∑ m ∈ Finset.Ioc A (Y - 1),
          |f (m + 1) - f m| * E := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (hprefix Y (Finset.mem_Icc.mpr ⟨hAY, le_rfl⟩))
          (abs_nonneg _)
      · calc
          |∑ m ∈ Finset.Ioc A (Y - 1),
              (f (m + 1) - f m) *
                (∑ k ∈ Finset.range (m + 1), c k)| <=
            ∑ m ∈ Finset.Ioc A (Y - 1),
              |(f (m + 1) - f m) *
                (∑ k ∈ Finset.range (m + 1), c k)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ <= ∑ m ∈ Finset.Ioc A (Y - 1),
              |f (m + 1) - f m| * E := by
            apply Finset.sum_le_sum
            intro m hm
            rw [abs_mul]
            apply mul_le_mul_of_nonneg_left
              (hprefix m (Finset.mem_Icc.mpr (by
                have hm' := Finset.mem_Ioc.mp hm
                constructor
                · exact hm'.1.le
                · omega)))
              (abs_nonneg _)
    _ = E * fourFiveRightDiscreteBVNorm f A Y := by
      unfold fourFiveRightDiscreteBVNorm
      rw [← Finset.sum_mul]
      ring

/-- Uniform cumulative reciprocal-prime discrepancy at every natural
endpoint beyond the safe cutoff. -/
theorem abs_fourFiveReciprocalPrimeDiscrepancy_le_uniform
    {A Y : Nat} (hA : fourFiveReciprocalBVSafeCutoff <= A)
    (hAY : A <= Y) :
    |fourFiveReciprocalPrimeDiscrepancy A Y| <=
      5 * fullReciprocalSumUniformConstant /
        Real.log (A : Real) ^ 3 := by
  unfold fourFiveReciprocalPrimeDiscrepancy fourFiveLogLogPrimitive
  exact fullReciprocalSumUniform_bound A Y
    (fourFiveReciprocalBVSafeCutoff_ge_uniformCutoff.trans hA) hAY

/-- Unconditional reciprocal-prime bounded-variation transfer.  The same
constant and cutoff work for every interval and every real-valued sequence;
only the displayed discrete BV norm of the sequence remains. -/
theorem abs_fourFiveReciprocalPrimeBVDefect_le_uniform
    (f : Nat -> Real) {A Y : Nat}
    (hA : fourFiveReciprocalBVSafeCutoff <= A) (hAY : A <= Y) :
    |fourFiveReciprocalPrimeBVDefect f A Y| <=
      (5 * fullReciprocalSumUniformConstant /
          Real.log (A : Real) ^ 3) *
        fourFiveRightDiscreteBVNorm f A Y := by
  have hA2 : 2 <= A :=
    fourFiveReciprocalBVSafeCutoff_ge_two.trans hA
  have hlogApos : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hE :
      0 <= 5 * fullReciprocalSumUniformConstant /
        Real.log (A : Real) ^ 3 := by
    exact div_nonneg
      (mul_nonneg (by norm_num) fullReciprocalSumUniformConstant_pos.le)
      (pow_nonneg hlogApos.le 3)
  apply abs_sum_Ioc_mul_le_prefixBound_mul_rightDiscreteBVNorm
    (fourFiveReciprocalPrimeSignedCell A) f hAY hE
  · rw [sum_range_fourFiveReciprocalPrimeSignedCell (A := A)
      (n := A) le_rfl]
    simp [fourFiveReciprocalPrimeDiscrepancy]
  · intro m hm
    rw [sum_range_fourFiveReciprocalPrimeSignedCell
      (A := A) (n := m) (Finset.mem_Icc.mp hm).1]
    exact abs_fourFiveReciprocalPrimeDiscrepancy_le_uniform hA
      (Finset.mem_Icc.mp hm).1



end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveProductMeasureTelescope -/
section


/-!
# The finite product-measure telescope in the four/five chamber

The ordered-prime argument replaces at most three reciprocal-prime
coordinates by their continuum log-log cell masses.  This file carries out
that replacement literally on the finite cell set `(A,Y]`.

There are two separate ingredients.

* `fourFiveFiniteProductOne/Two/Three` record the one-, two-, and
  three-coordinate product pairings.  Their subtraction identities are
  purely algebraic telescopes.
* The specializations to reciprocal-prime and log-log cell weights identify
  every telescope summand with the one-dimensional BV defect proved in
  `BankPaperFourFiveReciprocalPrimeBV`.  Absolute outer mass and discrete BV
  norms then give the losses `M^0`, `M^1`, and `M^2` for one, two, and three
  coordinates respectively.

No independence, positivity, smoothness, or analytic hypothesis is hidden in
the telescope identities.  The quantitative theorems ask only for the
displayed finite mass and conditional discrete-BV bounds.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open Erdos390.Full.PrimeBandQuadrature

/-! ## Generic finite product pairings and exact telescopes -/









/-- The literal two-term telescope replacing the first coordinate and then
the second coordinate. -/
theorem fourFiveFiniteProductTwo_sub
    {ι : Type*} (S : Finset ι) (a b : ι -> Real)
    (K : ι -> ι -> Real) :
    fourFiveFiniteProductTwo S a K -
        fourFiveFiniteProductTwo S b K =
      (∑ i ∈ S, (a i - b i) *
        (∑ j ∈ S, a j * K i j)) +
      ∑ i ∈ S, b i *
        (∑ j ∈ S, (a j - b j) * K i j) := by
  unfold fourFiveFiniteProductTwo
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i ∈ S,
        (a i * (∑ j ∈ S, a j * K i j) -
          b i * (∑ j ∈ S, b j * K i j))) =
        ∑ i ∈ S,
          ((a i - b i) * (∑ j ∈ S, a j * K i j) +
            b i * ((∑ j ∈ S, a j * K i j) -
              ∑ j ∈ S, b j * K i j)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = ∑ i ∈ S,
          ((a i - b i) * (∑ j ∈ S, a j * K i j) +
            b i * (∑ j ∈ S, (a j - b j) * K i j)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply congrArg (fun z : Real => b i * z)
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = (∑ i ∈ S, (a i - b i) *
          (∑ j ∈ S, a j * K i j)) +
        ∑ i ∈ S, b i *
          (∑ j ∈ S, (a j - b j) * K i j) :=
      Finset.sum_add_distrib

/-- The literal three-term telescope replacing the three coordinates from
left to right. -/
theorem fourFiveFiniteProductThree_sub
    {ι : Type*} (S : Finset ι) (a b : ι -> Real)
    (K : ι -> ι -> ι -> Real) :
    fourFiveFiniteProductThree S a K -
        fourFiveFiniteProductThree S b K =
      (∑ i ∈ S, (a i - b i) *
        (∑ j ∈ S, a j * (∑ k ∈ S, a k * K i j k))) +
      (∑ i ∈ S, b i *
        (∑ j ∈ S, (a j - b j) *
          (∑ k ∈ S, a k * K i j k))) +
      ∑ i ∈ S, b i *
        (∑ j ∈ S, b j *
          (∑ k ∈ S, (a k - b k) * K i j k)) := by
  unfold fourFiveFiniteProductThree
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i ∈ S,
        (a i * (∑ j ∈ S, a j * (∑ k ∈ S, a k * K i j k)) -
          b i * (∑ j ∈ S, b j * (∑ k ∈ S, b k * K i j k)))) =
        ∑ i ∈ S,
          ((a i - b i) *
              (∑ j ∈ S, a j * (∑ k ∈ S, a k * K i j k)) +
            b i *
              ((∑ j ∈ S, a j * (∑ k ∈ S, a k * K i j k)) -
                ∑ j ∈ S, b j * (∑ k ∈ S, b k * K i j k))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = ∑ i ∈ S,
          ((a i - b i) *
              (∑ j ∈ S, a j * (∑ k ∈ S, a k * K i j k)) +
            b i *
              ((∑ j ∈ S, (a j - b j) *
                  (∑ k ∈ S, a k * K i j k)) +
                ∑ j ∈ S, b j *
                  (∑ k ∈ S, (a k - b k) * K i j k))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      have htwo :
          (∑ j ∈ S, a j * (∑ k ∈ S, a k * K i j k)) -
              ∑ j ∈ S, b j * (∑ k ∈ S, b k * K i j k) =
            (∑ j ∈ S, (a j - b j) *
              (∑ k ∈ S, a k * K i j k)) +
              ∑ j ∈ S, b j *
                (∑ k ∈ S, (a k - b k) * K i j k) := by
        simpa only [fourFiveFiniteProductTwo] using
          fourFiveFiniteProductTwo_sub S a b (K i)
      rw [htwo]
    _ = (∑ i ∈ S, (a i - b i) *
          (∑ j ∈ S, a j * (∑ k ∈ S, a k * K i j k))) +
        (∑ i ∈ S, b i *
          (∑ j ∈ S, (a j - b j) *
            (∑ k ∈ S, a k * K i j k))) +
        ∑ i ∈ S, b i *
          (∑ j ∈ S, b j *
            (∑ k ∈ S, (a k - b k) * K i j k)) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      ring

/-! ## Two elementary norm ledgers -/

/-- A finite outer measure of absolute mass at most `M` carries a uniformly
bounded family at cost `M`. -/
theorem abs_fourFiveFiniteWeightedSum_le_mass_mul
    {ι : Type*} (S : Finset ι) (w g : ι -> Real)
    {M R : Real} (hmass : (∑ i ∈ S, |w i|) <= M)
    (hR : ∀ i ∈ S, |g i| <= R) (hR0 : 0 <= R) :
    |∑ i ∈ S, w i * g i| <= M * R := by
  calc
    |∑ i ∈ S, w i * g i| <=
        ∑ i ∈ S, |w i * g i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ S, |w i| * |g i| := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul]
    _ <= ∑ i ∈ S, |w i| * R := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hR i hi) (abs_nonneg _)
    _ = (∑ i ∈ S, |w i|) * R := by
      rw [Finset.sum_mul]
    _ <= M * R := mul_le_mul_of_nonneg_right hmass hR0

/-- Discrete right-BV is subadditive under a finite weighted family.  This
is the finite analogue of integrating conditional BV norms against total
variation. -/
theorem fourFiveRightDiscreteBVNorm_finiteWeightedFamily_le
    {ι : Type*} (S : Finset ι) (w : ι -> Real)
    (f : ι -> Nat -> Real) {A Y : Nat} {V : Real}
    (hV : ∀ i ∈ S,
      fourFiveRightDiscreteBVNorm (f i) A Y <= V)
    (_hV0 : 0 <= V) :
    fourFiveRightDiscreteBVNorm
        (fun n => ∑ i ∈ S, w i * f i n) A Y <=
      (∑ i ∈ S, |w i|) * V := by
  let D : Finset Nat := Finset.Ioc A (Y - 1)
  have hendpoint :
      |∑ i ∈ S, w i * f i Y| <=
        ∑ i ∈ S, |w i| * |f i Y| := by
    calc
      |∑ i ∈ S, w i * f i Y| <=
          ∑ i ∈ S, |w i * f i Y| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ S, |w i| * |f i Y| := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [abs_mul]
  have hvariation :
      (∑ m ∈ D,
          |(∑ i ∈ S, w i * f i (m + 1)) -
            ∑ i ∈ S, w i * f i m|) <=
        ∑ m ∈ D,
          ∑ i ∈ S, |w i| * |f i (m + 1) - f i m| := by
    apply Finset.sum_le_sum
    intro m _hm
    have hdiff :
        (∑ i ∈ S, w i * f i (m + 1)) -
            ∑ i ∈ S, w i * f i m =
          ∑ i ∈ S, w i * (f i (m + 1) - f i m) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    rw [hdiff]
    calc
      |∑ i ∈ S, w i * (f i (m + 1) - f i m)| <=
          ∑ i ∈ S, |w i * (f i (m + 1) - f i m)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ S, |w i| * |f i (m + 1) - f i m| := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [abs_mul]
  unfold fourFiveRightDiscreteBVNorm
  change
    |∑ i ∈ S, w i * f i Y| +
        ∑ m ∈ D,
          |(∑ i ∈ S, w i * f i (m + 1)) -
            ∑ i ∈ S, w i * f i m| <=
      (∑ i ∈ S, |w i|) * V
  calc
    |∑ i ∈ S, w i * f i Y| +
        ∑ m ∈ D,
          |(∑ i ∈ S, w i * f i (m + 1)) -
            ∑ i ∈ S, w i * f i m| <=
        (∑ i ∈ S, |w i| * |f i Y|) +
          ∑ m ∈ D,
            ∑ i ∈ S, |w i| * |f i (m + 1) - f i m| :=
      add_le_add hendpoint hvariation
    _ = ∑ i ∈ S, |w i| *
          (|f i Y| +
            ∑ m ∈ D, |f i (m + 1) - f i m|) := by
      simp_rw [mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
    _ <= ∑ i ∈ S, |w i| * V := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact hV i hi
    _ = (∑ i ∈ S, |w i|) * V := by
      rw [Finset.sum_mul]

/-- The preceding BV ledger with an externally supplied mass bound. -/
theorem fourFiveRightDiscreteBVNorm_finiteWeightedFamily_le_mass_mul
    {ι : Type*} (S : Finset ι) (w : ι -> Real)
    (f : ι -> Nat -> Real) {A Y : Nat} {M V : Real}
    (hmass : (∑ i ∈ S, |w i|) <= M)
    (hV : ∀ i ∈ S,
      fourFiveRightDiscreteBVNorm (f i) A Y <= V)
    (hV0 : 0 <= V) :
    fourFiveRightDiscreteBVNorm
        (fun n => ∑ i ∈ S, w i * f i n) A Y <= M * V := by
  exact (fourFiveRightDiscreteBVNorm_finiteWeightedFamily_le
    S w f hV hV0).trans
      (mul_le_mul_of_nonneg_right hmass hV0)

/-! ## Reciprocal-prime specialization -/



theorem fourFiveReciprocalBVError_pos
    {A : Nat} (hA : fourFiveReciprocalBVSafeCutoff <= A) :
    0 < fourFiveReciprocalBVError A := by
  have hA2 : 2 <= A :=
    fourFiveReciprocalBVSafeCutoff_ge_two.trans hA
  have hlogA : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  unfold fourFiveReciprocalBVError
  exact div_pos
    (mul_pos (by norm_num) fullReciprocalSumUniformConstant_pos)
    (pow_pos hlogA 3)

















/-- Exact three-coordinate telescope, displayed as three applications of
the one-dimensional signed-cell functional. -/
theorem fourFiveActualReciprocalProductThree_sub_continuum
    (K : Nat -> Nat -> Nat -> Real) (A Y : Nat) :
    fourFiveActualReciprocalProductThree K A Y -
        fourFiveContinuumLogLogProductThree K A Y =
      fourFiveReciprocalPrimeBVDefect
        (fun i => ∑ j ∈ Finset.Ioc A Y,
          fourFiveAnchoredReciprocalPrimeAtom A j *
            (∑ k ∈ Finset.Ioc A Y,
              fourFiveAnchoredReciprocalPrimeAtom A k * K i j k)) A Y +
      (∑ i ∈ Finset.Ioc A Y,
        fourFiveAnchoredLogLogCellAtom A i *
          fourFiveReciprocalPrimeBVDefect
            (fun j => ∑ k ∈ Finset.Ioc A Y,
              fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y) +
      ∑ i ∈ Finset.Ioc A Y,
        fourFiveAnchoredLogLogCellAtom A i *
          (∑ j ∈ Finset.Ioc A Y,
            fourFiveAnchoredLogLogCellAtom A j *
              fourFiveReciprocalPrimeBVDefect (K i j) A Y) := by
  unfold fourFiveActualReciprocalProductThree
    fourFiveContinuumLogLogProductThree
  rw [fourFiveFiniteProductThree_sub]
  unfold
    fourFiveReciprocalPrimeBVDefect
    fourFiveReciprocalPrimeSignedCell
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i _hi
      ring
    · apply Finset.sum_congr rfl
      intro i _hi
      apply congrArg (fun z : Real =>
        fourFiveAnchoredLogLogCellAtom A i * z)
      apply Finset.sum_congr rfl
      intro j _hj
      ring
  · apply Finset.sum_congr rfl
    intro i _hi
    apply congrArg (fun z : Real =>
      fourFiveAnchoredLogLogCellAtom A i * z)
    apply Finset.sum_congr rfl
    intro j _hj
    apply congrArg (fun z : Real =>
      fourFiveAnchoredLogLogCellAtom A j * z)
    apply Finset.sum_congr rfl
    intro k _hk
    ring

/-! ## Quantitative one-, two-, and three-coordinate transfer -/





/-- Three-coordinate product transfer.  This is the largest product
telescope needed in the four-to-five chamber. -/
theorem abs_fourFiveActualReciprocalProductThree_sub_continuum_le
    (K : Nat -> Nat -> Nat -> Real) {A Y : Nat} {M V : Real}
    (hA : fourFiveReciprocalBVSafeCutoff <= A) (hAY : A <= Y)
    (hactualMass :
      (∑ i ∈ Finset.Ioc A Y,
        |fourFiveAnchoredReciprocalPrimeAtom A i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc A Y,
        |fourFiveAnchoredLogLogCellAtom A i|) <= M)
    (hVfirst : ∀ j ∈ Finset.Ioc A Y,
      ∀ k ∈ Finset.Ioc A Y,
        fourFiveRightDiscreteBVNorm (fun i => K i j k) A Y <= V)
    (hVsecond : ∀ i ∈ Finset.Ioc A Y,
      ∀ k ∈ Finset.Ioc A Y,
        fourFiveRightDiscreteBVNorm (fun j => K i j k) A Y <= V)
    (hVthird : ∀ i ∈ Finset.Ioc A Y,
      ∀ j ∈ Finset.Ioc A Y,
        fourFiveRightDiscreteBVNorm (K i j) A Y <= V)
    (hV0 : 0 <= V) :
    |fourFiveActualReciprocalProductThree K A Y -
        fourFiveContinuumLogLogProductThree K A Y| <=
      3 * fourFiveReciprocalBVError A * M ^ 2 * V := by
  let S : Finset Nat := Finset.Ioc A Y
  let E : Real := fourFiveReciprocalBVError A
  have hE0 : 0 <= E := (fourFiveReciprocalBVError_pos hA).le
  have hM0 : 0 <= M := by
    exact (Finset.sum_nonneg fun i _hi => abs_nonneg
      (fourFiveAnchoredReciprocalPrimeAtom A i)).trans hactualMass
  have hfirstInner (j : Nat) (hj : j ∈ S) :
      fourFiveRightDiscreteBVNorm
          (fun i => ∑ k ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y <=
        M * V := by
    apply fourFiveRightDiscreteBVNorm_finiteWeightedFamily_le_mass_mul
      S (fourFiveAnchoredReciprocalPrimeAtom A)
        (fun k i => K i j k) hactualMass
    · intro k hk
      exact hVfirst j hj k hk
    · exact hV0
  have hfirstNorm :
      fourFiveRightDiscreteBVNorm
          (fun i => ∑ j ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A j *
              (∑ k ∈ S,
                fourFiveAnchoredReciprocalPrimeAtom A k * K i j k)) A Y <=
        M ^ 2 * V := by
    have hraw :=
      fourFiveRightDiscreteBVNorm_finiteWeightedFamily_le_mass_mul
        S (fourFiveAnchoredReciprocalPrimeAtom A)
          (fun j i => ∑ k ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A k * K i j k)
          hactualMass hfirstInner (mul_nonneg hM0 hV0)
    calc
      fourFiveRightDiscreteBVNorm
          (fun i => ∑ j ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A j *
              (∑ k ∈ S,
                fourFiveAnchoredReciprocalPrimeAtom A k * K i j k)) A Y <=
          M * (M * V) := hraw
      _ = M ^ 2 * V := by ring
  have hfirst :
      |fourFiveReciprocalPrimeBVDefect
        (fun i => ∑ j ∈ S,
          fourFiveAnchoredReciprocalPrimeAtom A j *
            (∑ k ∈ S,
              fourFiveAnchoredReciprocalPrimeAtom A k * K i j k)) A Y| <=
        E * (M ^ 2 * V) := by
    exact (abs_fourFiveReciprocalPrimeBVDefect_le_uniform _ hA hAY).trans
      (mul_le_mul_of_nonneg_left hfirstNorm hE0)
  have hsecondNorm (i : Nat) (hi : i ∈ S) :
      fourFiveRightDiscreteBVNorm
          (fun j => ∑ k ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y <=
        M * V := by
    apply fourFiveRightDiscreteBVNorm_finiteWeightedFamily_le_mass_mul
      S (fourFiveAnchoredReciprocalPrimeAtom A)
        (fun k j => K i j k) hactualMass
    · intro k hk
      exact hVsecond i hi k hk
    · exact hV0
  have hsecondInner (i : Nat) (hi : i ∈ S) :
      |fourFiveReciprocalPrimeBVDefect
        (fun j => ∑ k ∈ S,
          fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y| <=
        E * (M * V) := by
    exact (abs_fourFiveReciprocalPrimeBVDefect_le_uniform _ hA hAY).trans
      (mul_le_mul_of_nonneg_left (hsecondNorm i hi) hE0)
  have hsecond :
      |∑ i ∈ S, fourFiveAnchoredLogLogCellAtom A i *
        fourFiveReciprocalPrimeBVDefect
          (fun j => ∑ k ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y| <=
        M * (E * (M * V)) := by
    exact abs_fourFiveFiniteWeightedSum_le_mass_mul S
      (fourFiveAnchoredLogLogCellAtom A)
      (fun i => fourFiveReciprocalPrimeBVDefect
        (fun j => ∑ k ∈ S,
          fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y)
      hcontinuumMass hsecondInner
      (mul_nonneg hE0 (mul_nonneg hM0 hV0))
  have hthirdInner (i : Nat) (hi : i ∈ S)
      (j : Nat) (hj : j ∈ S) :
      |fourFiveReciprocalPrimeBVDefect (K i j) A Y| <= E * V := by
    exact (abs_fourFiveReciprocalPrimeBVDefect_le_uniform (K i j) hA hAY).trans
      (mul_le_mul_of_nonneg_left (hVthird i hi j hj) hE0)
  have hthirdMiddle (i : Nat) (hi : i ∈ S) :
      |∑ j ∈ S, fourFiveAnchoredLogLogCellAtom A j *
          fourFiveReciprocalPrimeBVDefect (K i j) A Y| <=
        M * (E * V) := by
    exact abs_fourFiveFiniteWeightedSum_le_mass_mul S
      (fourFiveAnchoredLogLogCellAtom A)
      (fun j => fourFiveReciprocalPrimeBVDefect (K i j) A Y)
      hcontinuumMass (hthirdInner i hi) (mul_nonneg hE0 hV0)
  have hthird :
      |∑ i ∈ S, fourFiveAnchoredLogLogCellAtom A i *
        (∑ j ∈ S, fourFiveAnchoredLogLogCellAtom A j *
          fourFiveReciprocalPrimeBVDefect (K i j) A Y)| <=
        M * (M * (E * V)) := by
    exact abs_fourFiveFiniteWeightedSum_le_mass_mul S
      (fourFiveAnchoredLogLogCellAtom A)
      (fun i => ∑ j ∈ S, fourFiveAnchoredLogLogCellAtom A j *
        fourFiveReciprocalPrimeBVDefect (K i j) A Y)
      hcontinuumMass hthirdMiddle
      (mul_nonneg hM0 (mul_nonneg hE0 hV0))
  rw [fourFiveActualReciprocalProductThree_sub_continuum]
  calc
    |fourFiveReciprocalPrimeBVDefect
          (fun i => ∑ j ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A j *
              (∑ k ∈ S,
                fourFiveAnchoredReciprocalPrimeAtom A k * K i j k)) A Y +
        (∑ i ∈ S, fourFiveAnchoredLogLogCellAtom A i *
          fourFiveReciprocalPrimeBVDefect
            (fun j => ∑ k ∈ S,
              fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y) +
        ∑ i ∈ S, fourFiveAnchoredLogLogCellAtom A i *
          (∑ j ∈ S, fourFiveAnchoredLogLogCellAtom A j *
            fourFiveReciprocalPrimeBVDefect (K i j) A Y)| <=
        |fourFiveReciprocalPrimeBVDefect
          (fun i => ∑ j ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A j *
              (∑ k ∈ S,
                fourFiveAnchoredReciprocalPrimeAtom A k * K i j k)) A Y| +
        |∑ i ∈ S, fourFiveAnchoredLogLogCellAtom A i *
          fourFiveReciprocalPrimeBVDefect
            (fun j => ∑ k ∈ S,
              fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y| +
        |∑ i ∈ S, fourFiveAnchoredLogLogCellAtom A i *
          (∑ j ∈ S, fourFiveAnchoredLogLogCellAtom A j *
            fourFiveReciprocalPrimeBVDefect (K i j) A Y)| := by
      exact (abs_add_three _ _ _)
    _ <= E * (M ^ 2 * V) + M * (E * (M * V)) +
        M * (M * (E * V)) := by
      exact add_le_add (add_le_add hfirst hsecond) hthird
    _ = 3 * fourFiveReciprocalBVError A * M ^ 2 * V := by
      dsimp [E]
      ring

end Erdos390.WholePaper.BankPaperRealization

end

theorem solution :
∀ (K : Nat → Nat → Nat → Real) {A Y : Nat} {M V : Real},
  LE.le.{0} Erdos390.WholePaper.BankPaperRealization.fourFiveReciprocalBVSafeCutoff A →
    LE.le.{0} A Y →
      LE.le.{0}
          (∑ i ∈ Finset.Ioc.{0} A Y,
            abs.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveAnchoredReciprocalPrimeAtom A i))
          M →
        LE.le.{0}
            (∑ i ∈ Finset.Ioc.{0} A Y,
              abs.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveAnchoredLogLogCellAtom A i))
            M →
          (∀ (j : Nat),
              Membership.mem.{0, 0} (Finset.Ioc.{0} A Y) j →
                ∀ (k : Nat),
                  Membership.mem.{0, 0} (Finset.Ioc.{0} A Y) k →
                    LE.le.{0}
                      (Erdos390.WholePaper.BankPaperRealization.fourFiveRightDiscreteBVNorm (fun i => K i j k) A Y) V) →
            (∀ (i : Nat),
                Membership.mem.{0, 0} (Finset.Ioc.{0} A Y) i →
                  ∀ (k : Nat),
                    Membership.mem.{0, 0} (Finset.Ioc.{0} A Y) k →
                      LE.le.{0}
                        (Erdos390.WholePaper.BankPaperRealization.fourFiveRightDiscreteBVNorm (fun j => K i j k) A Y)
                        V) →
              (∀ (i : Nat),
                  Membership.mem.{0, 0} (Finset.Ioc.{0} A Y) i →
                    ∀ (j : Nat),
                      Membership.mem.{0, 0} (Finset.Ioc.{0} A Y) j →
                        LE.le.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveRightDiscreteBVNorm (K i j) A Y)
                          V) →
                LE.le.{0} (0 : Real) V →
                  LE.le.{0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.WholePaper.BankPaperRealization.fourFiveActualReciprocalProductThree K A Y)
                        (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumLogLogProductThree K A Y)))
                    (HMul.hMul.{0, 0, 0}
                      (HMul.hMul.{0, 0, 0}
                        (HMul.hMul.{0, 0, 0} (3 : Real)
                          (Erdos390.WholePaper.BankPaperRealization.fourFiveReciprocalBVError A))
                        (HPow.hPow.{0, 0, 0} M (2 : Nat)))
                      V) := by
  exact @Erdos390.WholePaper.BankPaperRealization.abs_fourFiveActualReciprocalProductThree_sub_continuum_le
