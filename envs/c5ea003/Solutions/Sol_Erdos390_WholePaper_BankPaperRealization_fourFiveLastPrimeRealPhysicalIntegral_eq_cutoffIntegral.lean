-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.fourFiveLastPrimeRealPhysicalIntegral_eq_cutoffIntegral
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:54:08.287978+00:00
-- url     : https://prove2.me/submissions/ff7d93b8-12ba-4595-8292-7bcc221d6a6d

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_009

/- Source module: Erdos390.WholePaper.BankPaperFourFiveOrderedLastPrimeExpansion -/
section


/-!
# Exact last-prime expansion in the four/five chamber

This file exposes the last prime in each ordered layer before any analytic
approximation is made.  The existing finite reduction represents ordered
prime factors by lists.  Here those lists are identified with fixed-length
tuples, a tuple of length `m + 1` is split into its first `m` entries and its
last entry, and the last-entry fibre is identified with the literal prime
interval

`(max y (A / q), B / q]`,  where `q` is the prefix product.

The final theorem applies the uniform `pi-li` endpoint theorem at these exact
moving endpoints and sums its errors.  In particular, no relative estimate
for a short prime interval is used or assumed.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

/-! ## Fixed-length tuples and the existing ordered-list layer -/















/-! ## Splitting off the last coordinate -/





















/-! ## Every last-prime fibre is an exact clipped prime interval -/







/-- A prime prefix has positive product. -/
theorem fourFiveOrderedPrimePrefix_prod_pos
    {m y B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    0 < ∏ i, q i := by
  apply Finset.prod_pos
  intro i _hi
  exact (mem_fourFiveOrderedPrimePrefixSet.mp hq i).2.2.pos



/-! ## Applying the endpoint theorem fibrewise -/

















end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveRealLastPrimeEndpoint -/
section


/-!
# Real moving endpoints for the exposed last prime

The natural quotient endpoints used for the first exact cardinal expansion
are convenient combinatorially, but they introduce an avoidable unit-cell
rounding loss before the physical substitution `t = qv`.  The prime-counting
endpoint theorem accepts arbitrary real endpoints.  We therefore apply it at

`a = max y (A/q)` and `b = B/q`

in the real field.  Their natural floors are exactly the earlier quotient
endpoints, so the prime fibre is unchanged.  After this refinement the
physical substitution has the exact endpoints `max (q*y) A` and `B`.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization



theorem fourFiveRealPrefixProduct_pos
    {m y B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    0 < fourFiveRealPrefixProduct q := by
  unfold fourFiveRealPrefixProduct
  exact_mod_cast fourFiveOrderedPrimePrefix_prod_pos hq

















theorem fourFiveRealPrefixProduct_mul_realUpper
    {m y B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    fourFiveRealPrefixProduct q * fourFiveLastPrimeRealUpper q B =
      (B : Real) := by
  unfold fourFiveLastPrimeRealUpper
  exact mul_div_cancel₀ (B : Real) (fourFiveRealPrefixProduct_pos hq).ne'

theorem fourFiveRealPrefixProduct_mul_realLower
    {m y A B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    fourFiveRealPrefixProduct q * fourFiveLastPrimeRealLower q y A =
      max (fourFiveRealPrefixProduct q * (y : Real)) (A : Real) := by
  have hQnonneg : 0 <= fourFiveRealPrefixProduct q :=
    (fourFiveRealPrefixProduct_pos hq).le
  unfold fourFiveLastPrimeRealLower
  rw [mul_max_of_nonneg _ _ hQnonneg,
    mul_div_cancel₀ (A : Real) (fourFiveRealPrefixProduct_pos hq).ne']



/-- Endpoint-simplified form of the exact physical integral. -/
theorem fourFiveLastPrimeRealPhysicalIntegral_eq_maxIntegral
    {m y A B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    fourFiveLastPrimeRealPhysicalIntegral q y A B =
      if fourFiveLastPrimeRealLower q y A <=
          fourFiveLastPrimeRealUpper q B then
        (fourFiveRealPrefixProduct q)⁻¹ *
          ∫ t in
              max (fourFiveRealPrefixProduct q * (y : Real)) (A : Real)..
              (B : Real),
            1 / Real.log (t / fourFiveRealPrefixProduct q)
      else 0 := by
  unfold fourFiveLastPrimeRealPhysicalIntegral
  rw [fourFiveRealPrefixProduct_mul_realLower hq,
    fourFiveRealPrefixProduct_mul_realUpper hq]











/-! ## Quantitative fifth-log ledger -/



















end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveRealCommonDomainIdentification -/
section


/-!
# Exact common physical domain for the real last-prime endpoint

For a fixed prime prefix `q`, put `Q = prod_i q_i`.  The exact real
last-prime substitution has physical interval

`(max (Q*y) A, B]`.

This file rewrites that interval as the common outer interval `(A,B]`, with
the literal support cutoff `Q*y < t`.  The logarithmic identity

`log (t / Q) = log y * (log_y t - sum_i log_y q_i)`

then identifies the prefix summand with the moving-simplex kernel.  Finally,
finite prefix sums are commuted with the outer integral and, in dimensions
one, two, and three, the `Fin m` prefix sum is expanded into the nested
finite products already used by the product-measure telescope.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## A fixed-domain cutoff for one prefix -/



private theorem intervalIntegrable_of_measurable_of_abs_le_const_commonDomain
    {F : Real -> Real} {a b C : Real}
    (hF : Measurable F) (hbound : ∀ t ∈ Set.uIcc a b, |F t| <= C) :
    IntervalIntegrable F volume a b := by
  refine (intervalIntegrable_const (c := C)).mono_fun' ?_ ?_
  · exact hF.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    simpa only [Real.norm_eq_abs] using hbound t (Set.uIoc_subset_uIcc ht)

private theorem measurable_fourFiveRealPrefixCutoffKernel
    (Q : Real) (y : Nat) :
    Measurable (fourFiveRealPrefixCutoffKernel Q y) := by
  have hactive : MeasurableSet {t : Real | Q * (y : Real) < t} :=
    measurableSet_lt measurable_const measurable_id
  have hquot : Measurable (fun t : Real => t / Q) :=
    measurable_id.div_const Q
  have hkernel : Measurable (fun t : Real => 1 / Real.log (t / Q)) :=
    measurable_const.div (Real.measurable_log.comp hquot)
  unfold fourFiveRealPrefixCutoffKernel
  exact Measurable.ite hactive hkernel measurable_const

private theorem abs_fourFiveRealPrefixCutoffKernel_le
    {Q : Real} {y : Nat} (hQ : 0 < Q) (hy : 2 <= y) (t : Real) :
    |fourFiveRealPrefixCutoffKernel Q y t| <=
      1 / Real.log (y : Real) := by
  have hy1 : (1 : Real) < (y : Real) := by
    exact_mod_cast (show 1 < y by omega)
  have hlogy : 0 < Real.log (y : Real) := Real.log_pos hy1
  unfold fourFiveRealPrefixCutoffKernel
  split_ifs with ht
  · have hyquot : (y : Real) < t / Q := by
      exact (lt_div_iff₀ hQ).2 (by simpa [mul_comm] using ht)
    have hlogquot : Real.log (y : Real) < Real.log (t / Q) :=
      Real.log_lt_log (by positivity) hyquot
    have hquotpos : 0 < Real.log (t / Q) := hlogy.trans hlogquot
    rw [abs_of_pos (one_div_pos.mpr hquotpos)]
    exact one_div_le_one_div_of_le hlogy hlogquot.le
  · rw [abs_zero]
    exact one_div_nonneg.mpr hlogy.le

private theorem intervalIntegrable_fourFiveRealPrefixCutoffKernel
    {Q : Real} {y A B : Nat} (hQ : 0 < Q) (hy : 2 <= y) :
    IntervalIntegrable (fourFiveRealPrefixCutoffKernel Q y)
      volume (A : Real) (B : Real) := by
  apply intervalIntegrable_of_measurable_of_abs_le_const_commonDomain
    (measurable_fourFiveRealPrefixCutoffKernel Q y)
  intro t _ht
  exact abs_fourFiveRealPrefixCutoffKernel_le hQ hy t

private theorem fourFiveRealPrefixCutoffKernel_zero_left
    {Q : Real} {y A : Nat} (_hQ : 0 < Q) :
    (∫ t in (A : Real)..
        max (Q * (y : Real)) (A : Real),
      fourFiveRealPrefixCutoffKernel Q y t) = 0 := by
  by_cases hQA : Q * (y : Real) <= (A : Real)
  · rw [max_eq_right hQA]
    simp
  · have hAQ : (A : Real) <= Q * (y : Real) := le_of_not_ge hQA
    rw [max_eq_left hAQ]
    calc
      (∫ t in (A : Real)..(Q * (y : Real)),
          fourFiveRealPrefixCutoffKernel Q y t) =
        ∫ _t in (A : Real)..(Q * (y : Real)), (0 : Real) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have htIcc :
              t ∈ Set.Icc (A : Real) (Q * (y : Real)) := by
            rw [← Set.uIcc_of_le hAQ]
            exact ht
          unfold fourFiveRealPrefixCutoffKernel
          rw [if_neg]
          exact not_lt_of_ge htIcc.2
      _ = 0 := by simp

/-- A real last-prime physical integral is exactly its common-domain cutoff
integral.  No endpoint rounding remains. -/
theorem fourFiveLastPrimeRealPhysicalIntegral_eq_cutoffIntegral
    {m y A B : Nat} {q : Fin m -> Nat}
    (hy : 2 <= y) (_hyA : y <= A) (hAB : A <= B)
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    fourFiveLastPrimeRealPhysicalIntegral q y A B =
      (fourFiveRealPrefixProduct q)⁻¹ *
        ∫ t in (A : Real)..(B : Real),
          fourFiveRealPrefixCutoffKernel
            (fourFiveRealPrefixProduct q) y t := by
  have hQ : 0 < fourFiveRealPrefixProduct q :=
    fourFiveRealPrefixProduct_pos hq
  have hAB' : (A : Real) <= (B : Real) := by exact_mod_cast hAB
  rw [fourFiveLastPrimeRealPhysicalIntegral_eq_maxIntegral hq]
  by_cases hLU : fourFiveLastPrimeRealLower q y A <=
      fourFiveLastPrimeRealUpper q B
  · rw [if_pos hLU]
    have hLB : max (fourFiveRealPrefixProduct q * (y : Real)) (A : Real) <=
        (B : Real) := by
      calc
        max (fourFiveRealPrefixProduct q * (y : Real)) (A : Real) =
            fourFiveRealPrefixProduct q *
              fourFiveLastPrimeRealLower q y A :=
          (fourFiveRealPrefixProduct_mul_realLower hq).symm
        _ <= fourFiveRealPrefixProduct q *
              fourFiveLastPrimeRealUpper q B :=
          mul_le_mul_of_nonneg_left hLU hQ.le
        _ = (B : Real) := fourFiveRealPrefixProduct_mul_realUpper hq
    let L : Real :=
      max (fourFiveRealPrefixProduct q * (y : Real)) (A : Real)
    have hAL : (A : Real) <= L := le_max_right _ _
    have hcut := intervalIntegrable_fourFiveRealPrefixCutoffKernel
      (Q := fourFiveRealPrefixProduct q) (A := A) (B := B) hQ hy
    have hparts := (IntervalIntegrable.trans_iff
      (a := (A : Real)) (b := L) (c := (B : Real))
      (Set.mem_uIcc_of_le hAL hLB)).mp hcut
    have hright :
        (∫ t in L..(B : Real),
            fourFiveRealPrefixCutoffKernel
              (fourFiveRealPrefixProduct q) y t) =
          ∫ t in L..(B : Real),
            1 / Real.log (t / fourFiveRealPrefixProduct q) := by
      apply intervalIntegral.integral_congr_ae'
      · filter_upwards with t
        intro ht
        unfold fourFiveRealPrefixCutoffKernel
        rw [if_pos]
        exact (le_max_left _ _).trans_lt ht.1
      · filter_upwards with t
        intro ht
        exact (not_lt_of_ge (ht.2.trans hLB) ht.1).elim
    have hleft :
        (∫ t in (A : Real)..L,
          fourFiveRealPrefixCutoffKernel
            (fourFiveRealPrefixProduct q) y t) = 0 := by
      simpa [L] using fourFiveRealPrefixCutoffKernel_zero_left
        (Q := fourFiveRealPrefixProduct q) (y := y) (A := A) hQ
    calc
      (fourFiveRealPrefixProduct q)⁻¹ *
          (∫ t in L..(B : Real),
            1 / Real.log (t / fourFiveRealPrefixProduct q)) =
        (fourFiveRealPrefixProduct q)⁻¹ *
          (∫ t in L..(B : Real),
            fourFiveRealPrefixCutoffKernel
              (fourFiveRealPrefixProduct q) y t) := by rw [hright]
      _ = (fourFiveRealPrefixProduct q)⁻¹ *
          (∫ t in (A : Real)..(B : Real),
            fourFiveRealPrefixCutoffKernel
              (fourFiveRealPrefixProduct q) y t) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          hparts.1 hparts.2, hleft, zero_add]
  · rw [if_neg hLU]
    have hnotLB : ¬ (max (fourFiveRealPrefixProduct q * (y : Real))
        (A : Real) <= (B : Real)) := by
      intro hLB
      have hmul : fourFiveRealPrefixProduct q *
          fourFiveLastPrimeRealLower q y A <=
          fourFiveRealPrefixProduct q *
            fourFiveLastPrimeRealUpper q B := by
        simpa [fourFiveRealPrefixProduct_mul_realLower hq,
          fourFiveRealPrefixProduct_mul_realUpper hq] using hLB
      exact hLU ((mul_le_mul_iff_of_pos_left hQ).mp hmul)
    have hBy : (B : Real) <= fourFiveRealPrefixProduct q * (y : Real) := by
      have : (B : Real) <
          max (fourFiveRealPrefixProduct q * (y : Real)) (A : Real) :=
        lt_of_not_ge hnotLB
      rcases lt_max_iff.mp this with h | h
      · exact h.le
      · exact (not_lt_of_ge hAB' h).elim
    have hzero :
        (∫ t in (A : Real)..(B : Real),
          fourFiveRealPrefixCutoffKernel
            (fourFiveRealPrefixProduct q) y t) = 0 := by
      calc
        (∫ t in (A : Real)..(B : Real),
            fourFiveRealPrefixCutoffKernel
              (fourFiveRealPrefixProduct q) y t) =
          ∫ _t in (A : Real)..(B : Real), (0 : Real) := by
            apply intervalIntegral.integral_congr
            intro t ht
            have htIcc : t ∈ Set.Icc (A : Real) (B : Real) := by
              rw [← Set.uIcc_of_le hAB']
              exact ht
            unfold fourFiveRealPrefixCutoffKernel
            rw [if_neg]
            exact not_lt_of_ge (htIcc.2.trans hBy)
        _ = 0 := by simp
    rw [hzero, mul_zero]

/-! ## Logarithmic cancellation inside one prefix summand -/



















/-! ## Finite prefix sums in dimensions one, two, and three -/

















/-! ## Commuting the finite prefix sum with the outer integral -/



















/-! ## Integrated product replacement and vanishing overrun -/



























/-! ## Fully bounded real-endpoint bridge and factorial assembly -/

















end Erdos390.WholePaper.BankPaperRealization

end

theorem solution :
∀ {m y A B : Nat} {q : Fin m → Nat},
  LE.le.{0} (2 : Nat) y →
    LE.le.{0} y A →
      LE.le.{0} A B →
        Membership.mem.{0, 0} (Erdos390.WholePaper.BankPaperRealization.fourFiveOrderedPrimePrefixSet m y B) q →
          Eq.{1} (Erdos390.WholePaper.BankPaperRealization.fourFiveLastPrimeRealPhysicalIntegral q y A B)
            (HMul.hMul.{0, 0, 0} (Inv.inv.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveRealPrefixProduct q))
              (∫ (t : Real) in ↑A..↑B,
                Erdos390.WholePaper.BankPaperRealization.fourFiveRealPrefixCutoffKernel
                  (Erdos390.WholePaper.BankPaperRealization.fourFiveRealPrefixProduct q) y t)) := by
  exact @Erdos390.WholePaper.BankPaperRealization.fourFiveLastPrimeRealPhysicalIntegral_eq_cutoffIntegral
