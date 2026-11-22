-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_eventually_canonicalPhysical_powerCorrection_row_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:09:37.87425+00:00
-- url     : https://prove2.me/submissions/3c3f47f8-84d3-41a5-a951-795b50eb96b2

import Definitions.Def_erdos390_remaining_analytic_propositions_002
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_physicalPowerCorrectionMixtureBudget_le_inv_mul_rowError
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_sum_abs_actual_powerCorrection_sub_physicalMedium_le_compact
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound


section
universe u_1 u_2
theorem Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_actual_powerCorrection_sub_physicalMedium_le : Erdos390.AnalyticCompactBatch003Goal001.{u_1, u_2} := @Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_actual_powerCorrection_sub_physicalMedium_le_compact
end
/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)









theorem factor_ne_zero : P.factor ≠ 0 := by
  rw [factor]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (P.prime_mem p hp).ne_zero

theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.Full.PaperScaleMarkedCell -/
section


/-!
# Paper-scale common main term for marked structured cells

The raw structured-cell asymptotic is a finite sum of endpoint Dickman
terms.  This module performs the algebraic closure required in the paper:
the head Möbius coefficient is evaluated exactly, and the endpoint terms
are compared with one common Dickman translate before normalization.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.PaperScaleMarkedCell

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern MarkedFriableAsymptotic
open StructuredCellAsymptotic
open DivisibilityMomentBounds

noncomputable section

/-! ## Exact closure of the head Möbius coefficient -/











theorem headDensity_pos (P : Pattern) : 0 < headDensity P := by
  have hfactor : (0 : ℝ) < (P.factor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.factor_ne_zero
  have hmod : (0 : ℝ) < (P.modulus : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.modulus_ne_zero
  have htot : (0 : ℝ) < (P.modulus.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero P.modulus_ne_zero)
  exact mul_pos (one_div_pos.mpr hfactor) (div_pos htot hmod)



/-! ## The common paper-scale main term -/





theorem paperCellDensity_pos (P : Pattern) {A B : ℝ} (hAB : A < B) :
    0 < paperCellDensity P A B := by
  exact mul_pos (mul_pos (headDensity_pos P) (sub_pos.mpr hAB)) rho_U_pos

































/-! ## Normalization algebra -/







/-- The unmarked structured cell has a fixed positive linear density.  This
is the normalization lower bound used by all subsequent compact tilts. -/
theorem exists_structuredCell_density_lower_bound
    (P : Pattern) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ N₀ : ℕ, ∀ {n : ℕ}, N₀ ≤ n →
      paperCellDensity P A B * (n : ℝ) / 2 ≤
        ((structuredCell P (physicalBound A n) (physicalBound B n)
          (yNat n)).card : ℝ) := by
  obtain ⟨K, hK, Ncount, hcount⟩ :=
    exists_uniform_markedCell_paper_main_bound P hA hAB
  let c : ℝ := paperCellDensity P A B
  have hc : 0 < c := paperCellDensity_pos P hAB
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop,
      1 < n ∧ (2 : ℝ) ≤ y n ∧ 2 * K / c ≤ L n := by
    filter_upwards [Filter.eventually_gt_atTop 1,
      hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
      hLTop.eventually (Filter.eventually_ge_atTop (2 * K / c))] with
      n hn hy hden
    exact ⟨hn, hy, hden⟩
  obtain ⟨Nlarge, hNlarge⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨max Ncount Nlarge, ?_⟩
  intro n hN
  have hNc : Ncount ≤ n := by omega
  have hNl : Nlarge ≤ n := by omega
  obtain ⟨hn, hy, hden⟩ := hNlarge n hNl
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hL : 0 < L n := L_pos hn
  have hyNat2 : 2 ≤ yNat n := Nat.le_floor hy
  have h1d4 : 1 ≤ yNat n ^ 4 := by
    exact pow_pos (by omega : 0 < yNat n) 4
  have hbase₀ := hcount (n := n) (d := 1) hNc (by omega) h1d4
    (by simp [Nat.mem_smoothNumbers]) (by simp)
  have hbase :
      |((structuredCell P (physicalBound A n) (physicalBound B n)
          (yNat n)).card : ℝ) - c * (n : ℝ)| ≤
        K * (n : ℝ) / L n := by
    simpa [c, markedCell] using hbase₀
  have hscale : 2 * K ≤ c * L n := by
    have := (div_le_iff₀ hc).1 hden
    simpa [mul_comm] using this
  have hKdiv : K / L n ≤ c / 2 := by
    apply (div_le_iff₀ hL).2
    nlinarith [hscale]
  have herr : K * (n : ℝ) / L n ≤ c * (n : ℝ) / 2 := by
    calc
      K * (n : ℝ) / L n = (K / L n) * (n : ℝ) := by ring
      _ ≤ (c / 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hKdiv hnR.le
      _ = c * (n : ℝ) / 2 := by ring
  have hlower := (abs_le.mp (hbase.trans herr)).1
  dsimp only [c] at hlower ⊢
  linarith



end

end Erdos390.Full.PaperScaleMarkedCell

end

/- Source module: Erdos390.Full.PrimeSums -/
section


/-!
# Prime sums on the actual moving band

This file derives the finite prime-sum estimates needed in Lemma 7.5 from
Mathlib's Chebyshev bound.  No prime-sum estimate is introduced as a contract.
-/

open scoped BigOperators Nat.Prime
open Filter Topology

namespace Erdos390.Full.PrimeSums

open ArithmeticModel Scale



















private theorem primeBand_subset_primesUpTo (n W : ℕ) :
    primeBand n W ⊆ primesUpTo (yNat n) := by
  intro p hp
  have h := mem_primeBand.mp hp
  simp [primesUpTo, h.1, h.2.2]

















private theorem integral_one_div_mul_log {Y : ℝ} (hY : 2 ≤ Y) :
    (∫ t in (2 : ℝ)..Y, 1 / (t * Real.log t)) =
      Real.log (Real.log Y) - Real.log (Real.log 2) := by
  have hint : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t))
      MeasureTheory.volume 2 Y := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hY] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog0 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    exact ContinuousAt.continuousWithinAt
      (continuousAt_const.div (continuousAt_id.mul (Real.continuousAt_log ht0))
        (mul_ne_zero ht0 hlog0))
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint
  intro t ht
  rw [Set.uIcc_of_le hY] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hlog0 : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  have hd := (Real.hasDerivAt_log ht0).log hlog0
  convert hd using 1
  field_simp

/-- An explicit Mertens-type upper bound, obtained from the global Chebyshev
bound by Abel summation.  It is sufficient for every harmonic loss in
Lemma 7.5 and does not invoke the prime number theorem as an assumption. -/
theorem fullReciprocalSum_le (Y : ℕ) (hY : 2 ≤ Y) :
    fullReciprocalSum Y ≤
      2 * Real.log 4 + 3 * Real.log 4 *
        (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
  rw [fullReciprocalSum_eq Y hY]
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlogYhalf : (1 / 2 : ℝ) ≤ Real.log (Y : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (Y : ℝ) :=
      Real.log_le_log (by norm_num) hYR
    nlinarith [Real.log_two_gt_d9]
  have hlogY0 : 0 < Real.log (Y : ℝ) := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hboundary :
      Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) ≤
        2 * Real.log 4 := by
    calc
      Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) ≤
          (Real.log 4 * (Y : ℝ)) /
            ((Y : ℝ) * Real.log (Y : ℝ)) := by
        gcongr
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
      _ ≤ 2 * Real.log 4 := by
        field_simp [hY0.ne', hlogY0.ne']
        nlinarith
  have hint :
      (∫ t in (2 : ℝ)..Y,
        Chebyshev.theta t * (Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2)) ≤
        3 * Real.log 4 *
          (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
    calc
      (∫ t in (2 : ℝ)..Y,
        Chebyshev.theta t * (Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2)) ≤
          ∫ t in (2 : ℝ)..Y,
            3 * Real.log 4 * (1 / (t * Real.log t)) := by
        refine intervalIntegral.integral_mono_on hYR
          (intervalIntegrable_mertensIntegrand hYR) ?_ ?_
        · apply ContinuousOn.intervalIntegrable
          intro t ht
          rw [Set.uIcc_of_le hYR] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1]
          have hlog0 : Real.log t ≠ 0 :=
            Real.log_ne_zero_of_pos_of_ne_one
              (by linarith [ht.1]) (by linarith [ht.1])
          exact ContinuousAt.continuousWithinAt
            (continuousAt_const.mul
              (continuousAt_const.div
                (continuousAt_id.mul (Real.continuousAt_log ht0))
                (mul_ne_zero ht0 hlog0)))
        · intro t ht
          have ht0 : 0 < t := by linarith [ht.1]
          have hloghalf : (1 / 2 : ℝ) ≤ Real.log t := by
            have hmono : Real.log 2 ≤ Real.log t :=
              Real.log_le_log (by norm_num) ht.1
            nlinarith [Real.log_two_gt_d9]
          calc
            Chebyshev.theta t * (Real.log t + 1) /
                (t ^ 2 * Real.log t ^ 2) ≤
                (Real.log 4 * t) * (Real.log t + 1) /
                  (t ^ 2 * Real.log t ^ 2) := by
              gcongr
              exact Chebyshev.theta_le_log4_mul_x (le_of_lt ht0)
            _ ≤ 3 * Real.log 4 * (1 / (t * Real.log t)) := by
              field_simp [ht0.ne', (show Real.log t ≠ 0 by linarith)]
              nlinarith
      _ = 3 * Real.log 4 *
          (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
        rw [intervalIntegral.integral_const_mul, integral_one_div_mul_log hYR]
  linarith





theorem bandReciprocalSum_le_full (n W : ℕ) :
    bandReciprocalSum n W ≤ fullReciprocalSum (yNat n) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (primeBand_subset_primesUpTo n W)
  intro p hp hnot
  positivity

/-- The unweighted prime harmonic mass has precisely the `O(log L)` loss
allowed in Lemma 7.5.  The constant is explicit and independent of `W` and of
every later tilt box. -/
theorem eventually_bandReciprocalSum_le_logL (W : ℕ) :
    ∀ᶠ n in atTop,
      bandReciprocalSum n W ≤ 12 * Real.log (L n) := by
  have hyTop : Tendsto (fun n : ℕ => y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLTop : Tendsto (fun n : ℕ => Real.log (L n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hLTop
  have hlog4nonneg : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4upper : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog2pos : (0 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hinvLog2 : (Real.log 2)⁻¹ ≤ 2 := by
    rw [← one_div, one_div_le hlog2pos (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hloglog2 : (-1 : ℝ) ≤ Real.log (Real.log 2) := by
    calc
      (-1 : ℝ) ≤ 1 - (Real.log 2)⁻¹ := by linarith
      _ ≤ Real.log (Real.log 2) := Real.one_sub_inv_le_log_of_pos hlog2pos
  filter_upwards [eventually_gt_atTop 0,
    hyTop.eventually (eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually (eventually_ge_atTop (1 : ℝ)),
    hlogLTop.eventually (eventually_ge_atTop (5 : ℝ))] with n hn hyn hLn hlogLn
  have hyNat : 2 ≤ yNat n := Nat.le_floor hyn
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) := by positivity
  have hlogNatPos : 0 < Real.log (yNat n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < yNat n by omega))
  have hyFloor : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (le_of_lt (y_pos hn))
  have hlogNatLeY : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatPos hyFloor
  have hlogNatLeL : Real.log (yNat n : ℝ) ≤ L n := by
    calc
      Real.log (yNat n : ℝ) ≤ Real.log (y n) := hlogNatLeY
      _ = (2 / 9 : ℝ) * L n := log_y hn
      _ ≤ L n := by nlinarith
  have hloglogNatLeL :
      Real.log (Real.log (yNat n : ℝ)) ≤ Real.log (L n) :=
    Real.log_le_log hlogNatPos hlogNatLeL
  have hraw :
      bandReciprocalSum n W ≤
        2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (L n) - Real.log (Real.log 2)) := by
    calc
      bandReciprocalSum n W ≤ fullReciprocalSum (yNat n) :=
        bandReciprocalSum_le_full n W
      _ ≤ 2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (Real.log (yNat n : ℝ)) - Real.log (Real.log 2)) :=
        fullReciprocalSum_le (yNat n) hyNat
      _ ≤ 2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (L n) - Real.log (Real.log 2)) := by
        gcongr
  calc
    bandReciprocalSum n W ≤
        2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (L n) - Real.log (Real.log 2)) := hraw
    _ = Real.log 4 *
        (2 + 3 * Real.log (L n) - 3 * Real.log (Real.log 2)) := by ring
    _ ≤ Real.log 4 * (5 + 3 * Real.log (L n)) := by
      apply mul_le_mul_of_nonneg_left _ hlog4nonneg
      nlinarith
    _ ≤ 3 * (5 + 3 * Real.log (L n)) := by
      apply mul_le_mul_of_nonneg_right hlog4upper
      nlinarith
    _ ≤ 12 * Real.log (L n) := by nlinarith





end Erdos390.Full.PrimeSums

end

/- Source module: Erdos390.Full.LocalFugacityBounds -/
section


/-!
# Uniform bounds for restored local fugacity coefficients

The local restoration in Lemma 7.5 must retain both the factor `1 / L`
and the geometric factor `p^{-r}`.  Cardinality bounds on the exponent set
are too crude for that purpose.  This module proves the required shifted
geometric estimates directly for the actual coefficients
`exp (eta/L)^a - exp (eta/L)^(a-1)`.
-/

open scoped BigOperators

namespace Erdos390.Full.LocalFugacityBounds

open LocalFugacity

noncomputable section























theorem quadraticHalfMass_nonneg : 0 ≤ quadraticHalfMass := by
  unfold quadraticHalfMass
  exact tsum_nonneg fun i ↦ by
    unfold quadraticHalfTerm
    positivity



















end

end Erdos390.Full.LocalFugacityBounds

end

/- Source module: Erdos390.Full.PaperGuardCensus -/
section


/-!
# The concrete numerical-guard census used by the smooth bridge

The rough construction has only two kinds of numerical occurrences which can
meet one of the active smooth cells:

* promoted smooth anchors, in `O(y)` slots;
* endpoints (and the possible donor occurrence) of an `O(y)` family of bank
  paths, with at most one component at each geometric scale.

This file represents those occurrences by a literal finite slot type and
defines the numerical guard set as the image of its value map.  Consequently
the guard-cardinality estimate is a theorem about `Finset.image`; it is not a
field of a contract and it is not assumed about an arbitrary finset.

The number of geometric slots is fixed here to `ceil(log n)+1`.  This is a
harmless enlargement of the paper's geometric-scale list and makes the
`O(y log n)` census completely explicit.  Multiple slots are allowed to map to
the same integer; this only makes the proved image-cardinality bound stronger.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel Scale StructuredCells HeadPattern
open FiniteProbability GuardedUniformCell ValuationTiltCell

noncomputable section













/-- The global bridge-relevant guard census, derived from the image
construction rather than postulated. -/
theorem Ledger.card_guards_le {n Cprom Cbank : ℕ}
    (G : Ledger n Cprom Cbank) :
    G.guards.card ≤
      Cprom * yNat n + Cbank * yNat n * scaleSlots n * 3 := by
  calc
    G.guards.card ≤ (Finset.univ : Finset (GuardSlot n Cprom Cbank)).card :=
      Finset.card_image_le
    _ = Fintype.card (GuardSlot n Cprom Cbank) := Finset.card_univ
    _ = _ := card_guardSlot n Cprom Cbank

/-- The concrete ceiling has the advertised logarithmic size. -/
theorem cast_scaleSlots_lt {n : ℕ} (hn : 1 ≤ n) :
    (scaleSlots n : ℝ) < L n + 2 := by
  have hL : 0 ≤ L n := by
    unfold L
    exact Real.log_nonneg (by exact_mod_cast hn)
  unfold scaleSlots
  push_cast
  have hceil := Nat.ceil_lt_add_one hL
  linarith

/-- A weak inequality convenient in multiplicative census estimates. -/
theorem cast_scaleSlots_le {n : ℕ} (hn : 1 ≤ n) :
    (scaleSlots n : ℝ) ≤ L n + 2 :=
  (cast_scaleSlots_lt hn).le

/-- Real-cast form of the image census. -/
theorem Ledger.cast_card_guards_le {n Cprom Cbank : ℕ}
    (G : Ledger n Cprom Cbank) (hn : 1 ≤ n) :
    (G.guards.card : ℝ) ≤
      (Cprom + 3 * Cbank * (L n + 2)) * (yNat n : ℝ) := by
  have hcard : (G.guards.card : ℝ) ≤
      (Cprom * yNat n + Cbank * yNat n * scaleSlots n * 3 : ℕ) := by
    exact_mod_cast G.card_guards_le
  have hy0 : (0 : ℝ) ≤ (yNat n : ℝ) := by positivity
  have hscale := cast_scaleSlots_le hn
  calc
    (G.guards.card : ℝ) ≤
        (Cprom * yNat n + Cbank * yNat n * scaleSlots n * 3 : ℕ) := hcard
    _ = ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (scaleSlots n : ℝ)) *
          (yNat n : ℝ) := by
      push_cast
      ring
    _ ≤ ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) *
          (yNat n : ℝ) := by
      gcongr
    _ = (Cprom + 3 * Cbank * (L n + 2)) * (yNat n : ℝ) := by ring













end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.Full.PaperGuardedStructuredSample -/
section


/-!
# Canonical guarded structured sample

This module attaches the concrete guard ledger to the literal physical
structured cells used by the bridge.  Both physical endpoints are definitionally
`floor(A*n)`, and nonemptiness after guard deletion is derived from the proved
Dickman cell-density theorem and the concrete `O(y log n)` image census.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel Scale StructuredCells HeadPattern
open PaperScaleMarkedCell
open PaperBridgeFit

noncomputable section



variable {Head : Type*} [Fintype Head]





/-- Every raw cell has its proved positive Dickman density eventually. -/
theorem eventually_rawCell_density
    (P : Head → Pattern) (I : PhysicalIntervals) :
    ∀ᶠ n : ℕ in atTop, ∀ c : Cell Head,
      paperCellDensity (P c.1) (I.lower c.2) (I.upper c.2) *
          (n : ℝ) / 2 ≤ (rawCell P I n c).card := by
  rw [Filter.eventually_all]
  intro c
  obtain ⟨N₀, hN₀⟩ := exists_structuredCell_density_lower_bound
    (P c.1) (I.lower_pos c.2) (I.lower_lt_upper c.2)
  filter_upwards [eventually_ge_atTop N₀] with n hn
  simpa only [rawCell] using hN₀ hn























end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.Full.PaperBridgeNuisanceTiltFallback -/
section


/-!
# Marked fallback through the physical/head bridge tilt

On a fixed tagged bridge cell all centered-head coordinates are constant.
Consequently the residual nuisance tilt is exactly a small physical-log tilt;
the constant head factor cancels from normalization.  We combine that exact
identity with reciprocal divisibility bounds for the medium-prime tilt.

The resulting estimates retain the marked `1 / D` and `1 / (p q)` scales.
No total-variation estimate is used.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open ValuationScoreDomination OmittedTiltFallback
open DivisibilityMomentBounds

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

























/-- The actual guard-deleted cell endpoint is positive. -/
theorem cell_hi_pos (c : Cell Head) :
    0 < B.sampleData.hi c.2 := by
  obtain ⟨m, hm⟩ := B.sampleData.cell_nonempty c
  let sample : B.sampleData.Sample := ⟨c, ⟨m, hm⟩⟩
  have hmle : m ≤ B.sampleData.hi c.2 := by
    simpa only [sample, StructuredSampleData.value,
      StructuredSampleData.cellOf] using B.sampleData.value_le_hi sample
  have hmpos : 0 < m := by
    simpa only [sample, StructuredSampleData.value] using
      B.sampleData.value_pos sample
  exact hmpos.trans_le hmle











end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperGuardDeletionRows -/
section


/-!
# Prime-row perturbations from the concrete guard deletion

The central estimate is family-summed.  Thus the row cost is controlled by
the total valuation of one integer, `O(log n / log W)`, rather than by the
number of primes in the moving band.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel Scale StructuredCells HeadPattern
open FiniteProbability GuardedUniformCell
open ValuationTiltCell ArithmeticBandGeometry
open PaperScaleMarkedCell

noncomputable section

variable {Alpha I : Type*} [DecidableEq Alpha] [Fintype I]



/-- The concrete census-to-cell ratio, using the proved raw-cell density. -/
theorem guard_card_div_rawCell_le
    {Head : Type*} [Fintype Head]
    (P : Head → Pattern) (Iphys : PhysicalIntervals)
    {n Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (c : PaperBridgeFit.Cell Head) (hn : 1 ≤ n)
    (hdensity :
      paperCellDensity (P c.1) (Iphys.lower c.2) (Iphys.upper c.2) *
          (n : ℝ) / 2 ≤ (rawCell P Iphys n c).card) :
    (G.guards.card : ℝ) / ((rawCell P Iphys n c).card : ℝ) ≤
      2 * censusRatioMajorant Cprom Cbank n /
        paperCellDensity (P c.1) (Iphys.lower c.2) (Iphys.upper c.2) := by
  let density :=
    paperCellDensity (P c.1) (Iphys.lower c.2) (Iphys.upper c.2)
  have hdensityPos : 0 < density :=
    paperCellDensity_pos (P c.1) (Iphys.lower_lt_upper c.2)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hrawPos : 0 < ((rawCell P Iphys n c).card : ℝ) :=
    (div_pos (mul_pos hdensityPos hnR) (by norm_num)).trans_le hdensity
  have hguard := G.cast_card_guards_le hn
  have hyfloor : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (Scale.y_pos (by omega : 0 < n)).le
  have hcoef : 0 ≤
      (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by
    have hL : 0 ≤ L n := Real.log_nonneg (by exact_mod_cast hn)
    positivity
  have hguardY : (G.guards.card : ℝ) ≤
      ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) * y n :=
    hguard.trans (mul_le_mul_of_nonneg_left hyfloor hcoef)
  have hdivRaw :
      (G.guards.card : ℝ) / ((rawCell P Iphys n c).card : ℝ) ≤
        (G.guards.card : ℝ) / (density * (n : ℝ) / 2) := by
    exact div_le_div_of_nonneg_left (by positivity)
      (div_pos (mul_pos hdensityPos hnR) (by norm_num)) hdensity
  calc
    (G.guards.card : ℝ) / ((rawCell P Iphys n c).card : ℝ) ≤
        (G.guards.card : ℝ) / (density * (n : ℝ) / 2) := hdivRaw
    _ ≤ (((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) * y n) /
          (density * (n : ℝ) / 2) :=
      div_le_div_of_nonneg_right hguardY
        (div_nonneg (mul_nonneg hdensityPos.le hnR.le) (by norm_num))
    _ = 2 * censusRatioMajorant Cprom Cbank n / density := by
      unfold censusRatioMajorant
      field_simp [hdensityPos.ne', hnR.ne']















end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.Full.GuardSquarefreeErrorRate -/
section


/-!
# Vanishing rate of the squarefree guard error

The reciprocal guard conversion costs `y²`.  Since the concrete ledger has
`O(y log n)` guards and each raw cell has positive linear density, the final
cost is `O((log n)/n^(1/3))`; it still vanishes after multiplication by
`log log n`.  This file proves that rate with the literal scales.
-/

open Filter Topology

namespace Erdos390.Full.GuardSquarefreeErrorRate

open ArithmeticModel Scale PaperGuardCensus
open GuardDeletionSquarefreeProfiles

noncomputable section

private theorem tendsto_inv_nat_rpow_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) ^ a) atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (0 : ℝ) / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (0 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simp only [Function.comp_apply, Real.rpow_zero]

private theorem tendsto_L_div_nat_rpow_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ L n / (n : ℝ) ^ a) atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (1 : ℝ) / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simp only [Function.comp_apply, L, Real.rpow_one]



private theorem y_cube_div_nat_eq_inv_rpow {n : ℕ} (hn : 0 < n) :
    y n ^ 3 / (n : ℝ) = 1 / (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow :
      ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 3 *
          (n : ℝ) ^ (1 / 3 : ℝ) = (n : ℝ) := by
    calc
      ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 3 *
          (n : ℝ) ^ (1 / 3 : ℝ) =
        (((n : ℝ) ^ (2 / 9 : ℝ) *
            (n : ℝ) ^ (2 / 9 : ℝ)) *
          ((n : ℝ) ^ (2 / 9 : ℝ) *
            (n : ℝ) ^ (1 / 3 : ℝ))) := by ring
      _ = (n : ℝ) ^ ((2 / 9 : ℝ) + 2 / 9) *
          (n : ℝ) ^ ((2 / 9 : ℝ) + 1 / 3) := by
        rw [Real.rpow_add hnR, Real.rpow_add hnR]
      _ = (n : ℝ) ^ (((2 / 9 : ℝ) + 2 / 9) +
          ((2 / 9 : ℝ) + 1 / 3)) := by
        rw [← Real.rpow_add hnR]
      _ = (n : ℝ) := by norm_num [Real.rpow_one]
  unfold y
  field_simp [(Real.rpow_pos_of_pos hnR (1 / 3 : ℝ)).ne', hnR.ne']
  nlinarith

private theorem census_mul_y_sq_expansion
    (Cprom Cbank n : ℕ) (hn : 0 < n) :
    censusRatioMajorant Cprom Cbank n * y n ^ 2 =
      (Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
        3 * (Cbank : ℝ) *
          (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
            2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ))) := by
  rw [censusRatioMajorant]
  rw [show
    (((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) * y n /
        (n : ℝ)) * y n ^ 2 =
      ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) *
        (y n ^ 3 / (n : ℝ)) by ring]
  rw [y_cube_div_nat_eq_inv_rpow hn]
  ring

/-- The concrete census still vanishes after the reciprocal `y²` conversion. -/
theorem tendsto_censusRatioMajorant_mul_y_sq_zero (Cprom Cbank : ℕ) :
    Tendsto (fun n : ℕ ↦ censusRatioMajorant Cprom Cbank n * y n ^ 2)
      atTop (nhds 0) := by
  let a : ℝ := 1 / 3
  have ha : 0 < a := by norm_num [a]
  have hzero := tendsto_inv_nat_rpow_zero a ha
  have hlog := tendsto_L_div_nat_rpow_zero a ha
  have hsum : Tendsto
      (fun n : ℕ ↦
        (Cprom : ℝ) * (1 / (n : ℝ) ^ a) +
          3 * (Cbank : ℝ) *
            (L n / (n : ℝ) ^ a + 2 * (1 / (n : ℝ) ^ a)))
      atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      (hzero.const_mul (Cprom : ℝ)).add
        ((hlog.add (hzero.const_mul 2)).const_mul (3 * (Cbank : ℝ)))
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa only [a] using (census_mul_y_sq_expansion Cprom Cbank n hn).symm

/-- The unweighted census ratio itself tends to zero.  This follows from
the stronger `y²`-weighted estimate because `1 ≤ y²` eventually. -/
theorem tendsto_censusRatioMajorant_zero (Cprom Cbank : ℕ) :
    Tendsto (censusRatioMajorant Cprom Cbank) atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_
    (tendsto_censusRatioMajorant_mul_y_sq_zero Cprom Cbank)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    unfold censusRatioMajorant
    have hL : 0 ≤ L n := Real.log_nonneg (by exact_mod_cast hn)
    have hcoef : 0 ≤
        (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by positivity
    exact div_nonneg
      (mul_nonneg hcoef (Scale.y_pos hn).le) (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hyOne : (1 : ℝ) ≤ y n := by
      unfold y
      exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
    have hySq : (1 : ℝ) ≤ y n ^ 2 := by nlinarith
    have hcensus0 : 0 ≤ censusRatioMajorant Cprom Cbank n := by
      unfold censusRatioMajorant
      have hL : 0 ≤ L n := Real.log_nonneg (by exact_mod_cast hn)
      have hcoef : 0 ≤
          (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by positivity
      exact div_nonneg
        (mul_nonneg hcoef (Scale.y_pos hn).le) (by positivity)
    calc
      censusRatioMajorant Cprom Cbank n =
          censusRatioMajorant Cprom Cbank n * 1 := by ring
      _ ≤ censusRatioMajorant Cprom Cbank n * y n ^ 2 :=
        mul_le_mul_of_nonneg_left hySq hcensus0









/-- For a fixed score box, the concrete ledger has exponentially tilted
mass at most one half in every raw head/physical cell eventually. -/
theorem eventually_exp_two_mul_guardRatio_rawCell_le_half
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ c : PaperBridgeFit.Cell Head,
      Real.exp (2 * K) * ((G n).guards.card : ℝ) /
        ((rawCell P I n c).card : ℝ) ≤ (1 : ℝ) / 2 := by
  have hdensity := eventually_rawCell_density P I
  have hsmall : ∀ᶠ n : ℕ in atTop, ∀ c : PaperBridgeFit.Cell Head,
      (2 * Real.exp (2 * K) /
          PaperScaleMarkedCell.paperCellDensity (P c.1)
            (I.lower c.2) (I.upper c.2)) *
        censusRatioMajorant Cprom Cbank n ≤ (1 : ℝ) / 2 := by
    rw [Filter.eventually_all]
    intro c
    let constant := 2 * Real.exp (2 * K) /
      PaperScaleMarkedCell.paperCellDensity (P c.1)
        (I.lower c.2) (I.upper c.2)
    have hconst : Tendsto (fun _n : ℕ ↦ constant) atTop (nhds constant) :=
      tendsto_const_nhds
    have ht := hconst.mul
      (tendsto_censusRatioMajorant_zero Cprom Cbank)
    have ht0 : Tendsto (fun n : ℕ ↦
        (2 * Real.exp (2 * K) /
          PaperScaleMarkedCell.paperCellDensity (P c.1)
            (I.lower c.2) (I.upper c.2)) *
          censusRatioMajorant Cprom Cbank n) atTop (nhds 0) := by
      simpa only [constant, mul_zero] using ht
    exact ht0.eventually (eventually_le_nhds (by norm_num))
  filter_upwards [hdensity, hsmall, eventually_gt_atTop 0] with
      n hdens hsmalln hn c
  have hratio := guard_card_div_rawCell_le P I (G n) c
    (by omega : 1 ≤ n) (hdens c)
  have hexp0 : 0 ≤ Real.exp (2 * K) := (Real.exp_pos _).le
  calc
    Real.exp (2 * K) * ((G n).guards.card : ℝ) /
        ((rawCell P I n c).card : ℝ) =
      Real.exp (2 * K) *
        (((G n).guards.card : ℝ) / ((rawCell P I n c).card : ℝ)) := by ring
    _ ≤ Real.exp (2 * K) *
        (2 * censusRatioMajorant Cprom Cbank n /
          PaperScaleMarkedCell.paperCellDensity (P c.1)
            (I.lower c.2) (I.upper c.2)) :=
      mul_le_mul_of_nonneg_left hratio hexp0
    _ = (2 * Real.exp (2 * K) /
          PaperScaleMarkedCell.paperCellDensity (P c.1)
            (I.lower c.2) (I.upper c.2)) *
        censusRatioMajorant Cprom Cbank n := by ring
    _ ≤ (1 : ℝ) / 2 := hsmalln c

/-- After deleting the concrete guard ledger, every fixed head/physical cell
still retains a fixed positive fraction of its proved raw density.  The
constant `1/4` is uniform over the finite family of cells and is stated at
the literal finite-`n` cardinality level. -/
theorem eventually_guarded_rawCell_density
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank) :
    ∀ᶠ n : ℕ in atTop, ∀ c : PaperBridgeFit.Cell Head,
      PaperScaleMarkedCell.paperCellDensity (P c.1)
          (I.lower c.2) (I.upper c.2) * (n : ℝ) / 4 ≤
        ((rawCell P I n c \ (G n).guards).card : ℝ) := by
  have hdensity := eventually_rawCell_density P I
  have hguardRatio :=
    eventually_exp_two_mul_guardRatio_rawCell_le_half
      P I Cprom Cbank G 0
  filter_upwards [hdensity, hguardRatio, eventually_gt_atTop 0] with
      n hdens hratio hn c
  let density := PaperScaleMarkedCell.paperCellDensity (P c.1)
    (I.lower c.2) (I.upper c.2)
  let S := rawCell P I n c
  let R := S \ (G n).guards
  have hdensityPos : 0 < density := by
    exact PaperScaleMarkedCell.paperCellDensity_pos
      (P c.1) (I.lower_lt_upper c.2)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by
    have hmain : 0 < density * (n : ℝ) / 2 := by positivity
    exact hmain.trans_le (by simpa only [density, S] using hdens c)
  have hratio' : ((G n).guards.card : ℝ) / (S.card : ℝ) ≤
      (1 : ℝ) / 2 := by
    have hc := hratio c
    norm_num at hc
    simpa only [S] using hc
  have hguard : ((G n).guards.card : ℝ) ≤ (S.card : ℝ) / 2 := by
    have := (div_le_iff₀ hSpos).mp hratio'
    nlinarith
  have hcardNat : S.card ≤ R.card + (G n).guards.card := by
    simpa only [R] using
      (Finset.card_le_card_sdiff_add_card
        (s := S) (t := (G n).guards))
  have hcardReal : (S.card : ℝ) ≤ (R.card : ℝ) +
      ((G n).guards.card : ℝ) := by exact_mod_cast hcardNat
  have hraw : density * (n : ℝ) / 2 ≤ (S.card : ℝ) := by
    simpa only [density, S] using hdens c
  have : density * (n : ℝ) / 4 ≤ (R.card : ℝ) := by
    nlinarith
  simpa only [density, S, R] using this

/-- Endpoint-normalized form of `eventually_guarded_rawCell_density`.  Each
fixed cell gets the explicit positive density
`paperCellDensity/(4*upper)`; no minimum over a varying family is used. -/
theorem eventually_guarded_rawCell_endpoint_density
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank) :
    ∀ᶠ n : ℕ in atTop, ∀ c : PaperBridgeFit.Cell Head,
      let rho := PaperScaleMarkedCell.paperCellDensity (P c.1)
        (I.lower c.2) (I.upper c.2) / (4 * I.upper c.2)
      0 < rho ∧
        rho * (physicalBound (I.upper c.2) n : ℝ) ≤
          ((rawCell P I n c \ (G n).guards).card : ℝ) := by
  have hdensity := eventually_guarded_rawCell_density P I Cprom Cbank G
  filter_upwards [hdensity] with n hdens c
  let density := PaperScaleMarkedCell.paperCellDensity (P c.1)
    (I.lower c.2) (I.upper c.2)
  let upper := I.upper c.2
  let rho := density / (4 * upper)
  have hdensityPos : 0 < density := by
    exact PaperScaleMarkedCell.paperCellDensity_pos
      (P c.1) (I.lower_lt_upper c.2)
  have hupperPos : 0 < upper := by
    exact (I.lower_pos c.2).trans (I.lower_lt_upper c.2)
  have hrho : 0 < rho := by
    exact div_pos hdensityPos (mul_pos (by norm_num) hupperPos)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hbound : (physicalBound upper n : ℝ) ≤ upper * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hupperPos.le hn0)
  have hscaled : rho * (physicalBound upper n : ℝ) ≤
      density * (n : ℝ) / 4 := by
    calc
      rho * (physicalBound upper n : ℝ) ≤ rho * (upper * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound hrho.le
      _ = density * (n : ℝ) / 4 := by
        dsimp only [rho]
        field_simp [hupperPos.ne']
  refine ⟨hrho, hscaled.trans ?_⟩
  simpa only [density, upper] using hdens c









end

end Erdos390.Full.GuardSquarefreeErrorRate

end

/- Source module: Erdos390.Full.PaperActualSquarefreeReference -/
section


/-!
# The actual bridge squarefree law and the canonical reference operator

This file closes two finite-probability identifications needed in Lemma 8.4.
First, a reciprocal signed profile for the medium-only law survives the
literal physical/head component tilt at the same reciprocal scale.  Second,
the partition-function-reweighted mixture of those component laws is exactly
the `BridgeData.tiltedLaw`, including the between-cell covariance.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open OmittedTiltPairChamber PaperPrimePowerChamberError
open StructuredCells ValuationScoreDomination

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











/-- The exponential reciprocal fallback used by the physical second tilt is
bounded by the same fixed effective-prime box constant as the raw medium
score.  In particular the ceiling has no dependence on `n` or on a moving
band cell. -/
theorem mediumFallbackExponent_le [Nonempty Head]
    (c : Cell Head) {C A : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W) (hA : 0 ≤ A)
    (hhi : B.sampleData.hi c.2 ≤
      physicalBound C B.sampleData.n) :
    (A / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)) ≤
      A * PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W := by
  have hhiPos : (0 : ℝ) < B.sampleData.hi c.2 := by
    exact_mod_cast B.cell_hi_pos c
  have hboundPos : (0 : ℝ) < physicalBound C B.sampleData.n := by
    have hn : 0 < B.sampleData.n := Nat.zero_lt_of_lt B.n_gt_one
    have hnle : B.sampleData.n ≤ physicalBound C B.sampleData.n := by
      unfold physicalBound
      apply Nat.le_floor
      exact_mod_cast (show (B.sampleData.n : ℝ) ≤
        C * (B.sampleData.n : ℝ) by
          nlinarith [show (0 : ℝ) ≤ (B.sampleData.n : ℝ) by positivity])
    exact_mod_cast hn.trans_le hnle
  have hlogW : 0 < Real.log (B.sampleData.W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hlogHi : Real.log (B.sampleData.hi c.2 : ℝ) ≤
      PaperStatisticNorm.physicalLogCoefficient C * B.L := by
    exact (Real.log_le_log hhiPos (by exact_mod_cast hhi)).trans
      (PaperStatisticNorm.BridgeData.log_physicalBound_le B hC)
  have hratio :
      Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ) ≤
        (PaperStatisticNorm.physicalLogCoefficient C * B.L) /
          Real.log (B.sampleData.W : ℝ) :=
    div_le_div_of_nonneg_right hlogHi hlogW.le
  calc
    (A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)) ≤
        (A / B.L) *
          ((PaperStatisticNorm.physicalLogCoefficient C * B.L) /
            Real.log (B.sampleData.W : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (div_nonneg hA B.L_pos.le)
    _ = A * PaperStatisticNorm.valuationLogCoefficient C
          B.sampleData.W := by
      unfold PaperStatisticNorm.valuationLogCoefficient
      field_simp [B.L_pos.ne', hlogW.ne']

























/-! ### Exact finite-dimensional attachment to the arithmetic inverse -/



























/-! ### Reference-law row attachment

The literal global-tilt form of Lemma 7.5 is naturally obtained first for an
unguarded component mixture.  The actual bridge law is a guard-deleted
mixture with a residual physical tilt.  The next elementary estimate keeps
that identification issue outside the prime-power algebra: a weighted
prime-row comparison for the full and squarefree covariance matrices moves
the Lemma 7.5 estimate from an arbitrary reference law to the actual law.
The only moving-low loss is displayed explicitly as `rho / center i`.
-/





















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBridgePhysicalPowerCorrectionRow -/
section


/-!
# The prime-power correction row through the residual physical tilt

This file keeps the actual partition-function-reweighted component weights
fixed and compares the residual physical tilt component by component.  The
high prime-power columns are summed geometrically before the tagged-mixture
covariance algebra is applied.  Consequently the final comparison is for the
literal `VV-II` row, including all between-component covariance terms.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PrimePowerCutoffCovariance ValuationCutoff LocalFugacityBounds
open PrimeSums
open PrimePowerLcmGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)







theorem physicalPowerCorrectionRowError_nonneg
    {epsilon G : ℝ} {n W : ℕ}
    (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G) :
    0 ≤ physicalPowerCorrectionRowError epsilon G n W := by
  unfold physicalPowerCorrectionRowError bandReciprocalSum
  have hQ : 0 ≤ quadraticHalfMass := quadraticHalfMass_nonneg
  positivity

/-- The residual-physical prime-power row retains the sharp moving-low-cell
rate.  The hypothesis is deliberately the two-harmonic rate: one logarithm
is spent in the prime-row sum and the displayed factor spends the second.
Thus this theorem does not silently promote a bare `o(1)` bound to the
`o(alpha_0)` bound needed in Lemma 8.5. -/
theorem tendsto_physicalPowerCorrectionRowError_mul_logL_zero
    (epsilon : ℕ → ℝ) (G : ℝ) (W : ℕ)
    (hepsilon0 : ∀ n, 0 ≤ epsilon n) (hG : 0 ≤ G)
    (hepsilonRateSq : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n) ^ 2)
        atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦
      physicalPowerCorrectionRowError (epsilon n) G n W *
        Real.log (Scale.L n)) atTop (nhds 0) := by
  let C : ℝ :=
    200 * 8 * (1 + quadraticHalfMass) * (1 + G) ^ 2 *
      (1 / (W : ℝ))
  let upper : ℕ → ℝ := fun n ↦
    (13 * C) * (epsilon n * Real.log (Scale.L n) ^ 2)
  have hQ : 0 ≤ quadraticHalfMass := quadraticHalfMass_nonneg
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hupperT : Tendsto upper atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦ 13 * C) atTop (nhds (13 * C)) :=
      tendsto_const_nhds
    have hraw := hconst.mul hepsilonRateSq
    simpa only [upper, mul_zero] using hraw
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ physicalPowerCorrectionRowError (epsilon n) G n W *
        Real.log (Scale.L n) := by
    filter_upwards [hLTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hL
    exact mul_nonneg
      (physicalPowerCorrectionRowError_nonneg (hepsilon0 n) hG)
      (Real.log_nonneg hL)
  have hmajor : ∀ᶠ n : ℕ in atTop,
      physicalPowerCorrectionRowError (epsilon n) G n W *
          Real.log (Scale.L n) ≤ upper n := by
    filter_upwards [eventually_bandReciprocalSum_le_logL W,
      hLTop.eventually (eventually_ge_atTop (Real.exp 1))]
      with n hband hL
    have hlog : 1 ≤ Real.log (Scale.L n) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hL
    have hlog0 : 0 ≤ Real.log (Scale.L n) := le_trans (by norm_num) hlog
    have hband0 : 0 ≤ bandReciprocalSum n W := by
      unfold bandReciprocalSum
      positivity
    have hbandOne : bandReciprocalSum n W + 1 ≤
        13 * Real.log (Scale.L n) := by linarith
    have hscale : 0 ≤ C * epsilon n := mul_nonneg hC (hepsilon0 n)
    have hscaled := mul_le_mul_of_nonneg_left hbandOne hscale
    dsimp only [upper]
    unfold physicalPowerCorrectionRowError
    dsimp only [C]
    calc
      (200 * (8 * epsilon n) * (1 + quadraticHalfMass) *
          (1 + G) ^ 2 * (bandReciprocalSum n W + 1) *
            (1 / (W : ℝ))) * Real.log (Scale.L n) =
          (C * epsilon n) * (bandReciprocalSum n W + 1) *
            Real.log (Scale.L n) := by ring
      _ ≤ (C * epsilon n) * (13 * Real.log (Scale.L n)) *
            Real.log (Scale.L n) :=
        mul_le_mul_of_nonneg_right hscaled hlog0
      _ = (13 * C) *
          (epsilon n * Real.log (Scale.L n) ^ 2) := by ring
  exact squeeze_zero' hnonneg hmajor hupperT





/-- Weighted-row form of the preceding exact contraction. -/
theorem physicalPowerCorrectionMixtureBudget_mul_le_rowError
    {epsilon G : ℝ} {n W p : ℕ}
    (hepsilon : 0 ≤ epsilon) (hsmall : 8 * epsilon ≤ 1)
    (hG : 0 ≤ G) (hW : 1 < W) (hp : p ∈ primeBand n W) :
    (p : ℝ) * physicalPowerCorrectionMixtureBudget epsilon G n W p ≤
      physicalPowerCorrectionRowError epsilon G n W := by
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  have hpne : (p : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand hp).ne_zero
  calc
    (p : ℝ) * physicalPowerCorrectionMixtureBudget epsilon G n W p ≤
        (p : ℝ) * ((1 / (p : ℝ)) *
          physicalPowerCorrectionRowError epsilon G n W) :=
      mul_le_mul_of_nonneg_left
        (physicalPowerCorrectionMixtureBudget_le_inv_mul_rowError
          hepsilon hsmall hG hW hp) hp0
    _ = physicalPowerCorrectionRowError epsilon G n W := by
      field_simp



































/-- Literal weighted prime row for the residual physical tilt.  This is the
concrete `rhoPower` input used by the full-versus-squarefree bridge theorem. -/
theorem actual_powerCorrection_physicalMedium_weightedRow_le
    [Nonempty Head]
    (xi : B.ParamSpace)
    (rho : Cell Head → ℝ)
    {A Aphys Kphys G : ℝ}
    (hA : 0 ≤ A) (hAphys0 : 0 ≤ Aphys) (hKphys0 : 0 ≤ Kphys)
    (hG : 0 ≤ G) (hW : 1 < B.sampleData.W)
    (hrho : ∀ c, 0 < rho c)
    (hcard : ∀ c, rho c * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hKphys : ∀ c (m : B.sampleData.SampleAt c),
      |B.physicalScore ⟨c, m⟩| ≤ Kphys)
    (hsmall : 8 * (Aphys * Kphys / B.L) ≤ 1)
    (hGdom : ∀ c,
      Real.exp (2 * ((A / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)))) / rho c ≤ G)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    (p.1 : ℝ) *
      (∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1) -
          ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
            (B.physicalMediumReferenceLaw xi).covII p.1 q.1)|) ≤
      physicalPowerCorrectionRowError
        (Aphys * Kphys / B.L) G
          B.sampleData.n B.sampleData.W := by
  have hepsilon : 0 ≤ Aphys * Kphys / B.L :=
    div_nonneg (mul_nonneg hAphys0 hKphys0) B.L_pos.le
  have hsum := B.sum_abs_actual_powerCorrection_sub_physicalMedium_le
    xi rho hA hAphys0 hKphys0 hG hW hrho hcard heta hAphys hKphys
      hsmall hGdom p
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ (p.1 : ℝ) by positivity)
  exact hscaled.trans
    (physicalPowerCorrectionMixtureBudget_mul_le_rowError
      hepsilon hsmall hG hW p.2)



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBridgeCanonicalPhysicalPowerCorrectionEventually -/
section


/-!
# Eventual canonical specialization of the residual physical power row

This file discharges the density, score-envelope, small-tilt, and divisor
fallback inputs of the residual-physical comparison.  All constants are
chosen from the fixed physical cells, cutoff, and preselected coefficient
box.  The resulting row error is also proved to survive division by the
moving-low centre, via its explicit `error * log L -> 0` rate.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums

namespace BridgeData

variable {Head : Type*} [Fintype Head] [DecidableEq Head]







omit [Fintype Head] [DecidableEq Head] in
theorem canonicalPhysicalCellDensity_pos
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (c : Cell Head) :
    0 < canonicalPhysicalCellDensity P I c := by
  unfold canonicalPhysicalCellDensity
  exact div_pos
    (PaperScaleMarkedCell.paperCellDensity_pos
      (P c.1) (I.lower_lt_upper c.2))
    (mul_pos (by norm_num)
      ((I.lower_pos c.2).trans (I.lower_lt_upper c.2)))

omit [DecidableEq Head] in
theorem canonicalPhysicalPowerCorrectionConstant_nonneg
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (W : ℕ) (Acoef : ℝ) :
    0 ≤ canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef := by
  unfold canonicalPhysicalPowerCorrectionConstant
  exact Finset.sum_nonneg fun c _ ↦
    div_nonneg (Real.exp_pos _).le
      (canonicalPhysicalCellDensity_pos P I c).le

/-- A fixed multiple of `1/L` survives both harmonic losses required by the
residual-physical row lemma. -/
theorem tendsto_canonicalPhysicalPowerCorrectionEpsilon_mul_logL_sq_zero
    (Aphys Cmax : ℝ) :
    Tendsto (fun n : ℕ ↦
      canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n *
        Real.log (Scale.L n) ^ 2) atTop (nhds 0) := by
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto
      (fun n : ℕ ↦ Real.log (Scale.L n) ^ 2 / Scale.L n)
        atTop (nhds 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hconst : Tendsto
      (fun _n : ℕ ↦ Aphys * Real.log Cmax) atTop
        (nhds (Aphys * Real.log Cmax)) := tendsto_const_nhds
  have hmul := hconst.mul hratio
  apply (show Tendsto (fun n : ℕ ↦
      (Aphys * Real.log Cmax) *
        (Real.log (Scale.L n) ^ 2 / Scale.L n))
      atTop (nhds 0) by simpa only [mul_zero] using hmul).congr'
  filter_upwards with n
  unfold canonicalPhysicalPowerCorrectionEpsilon
  ring

/-- Fully discharged canonical residual-physical row comparison.

The threshold is independent of the later band partition, bridge data, tilt
point, and prime row.  The only call-site hypotheses are the exact canonical
constructor equality and the two genuine coefficient-box inequalities. -/
theorem exists_eventually_canonicalPhysical_powerCorrection_row
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (Acoef Aphys : ℝ) (hAcoef : 0 ≤ Acoef) (hAphys0 : 0 ≤ Aphys) :
    let G := canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef
    let epsilon := canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax
    0 ≤ G ∧
      Tendsto (fun n : ℕ ↦
        physicalPowerCorrectionRowError (epsilon n) G n W *
          Real.log (Scale.L n)) atTop (nhds 0) ∧
      ∃ N₀ : ℕ,
        ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
          (B : BridgeData Head Band) (xi : B.ParamSpace),
          N₀ ≤ B.sampleData.n →
          B.sampleData.W = W →
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell P I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            B.sampleData = canonicalSampleData (W := B.sampleData.W)
                P I (ledger B.sampleData.n) hsep hremaining →
            (∀ p : BandPrime B.sampleData.n B.sampleData.W,
              |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
            |xi MomentCoord.physical| ≤ Aphys →
            ∀ p : BandPrime B.sampleData.n B.sampleData.W,
              (p.1 : ℝ) *
                (∑ q : BandPrime B.sampleData.n B.sampleData.W,
                  |((B.actualValuationLaw xi).covVV p.1 q.1 -
                      (B.actualValuationLaw xi).covII p.1 q.1) -
                    ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
                      (B.physicalMediumReferenceLaw xi).covII p.1 q.1)|) ≤
                physicalPowerCorrectionRowError
                  (epsilon B.sampleData.n) G
                    B.sampleData.n B.sampleData.W := by
  dsimp only
  let G := canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef
  let epsilon := canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax
  have hupperOne : ∀ sigma, 1 ≤ I.upper sigma := fun sigma ↦
    (hlowerOne sigma).trans (I.lower_lt_upper sigma).le
  have hCmax : 1 ≤ Cmax :=
    (hupperOne .minus).trans (hupperMax .minus)
  have hlogC0 : 0 ≤ Real.log Cmax := Real.log_nonneg hCmax
  have hL0 (n : ℕ) : 0 ≤ Scale.L n := by
    cases n with
    | zero => norm_num [Scale.L]
    | succ n =>
        exact Real.log_nonneg (by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
  have hG : 0 ≤ G := by
    exact canonicalPhysicalPowerCorrectionConstant_nonneg P I Cmax W Acoef
  have hepsilon0 (n : ℕ) : 0 ≤ epsilon n := by
    dsimp only [epsilon, canonicalPhysicalPowerCorrectionEpsilon]
    exact div_nonneg (mul_nonneg hAphys0 hlogC0) (hL0 n)
  have hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n) ^ 2)
        atTop (nhds 0) := by
    exact tendsto_canonicalPhysicalPowerCorrectionEpsilon_mul_logL_sq_zero
      Aphys Cmax
  have hrowRate :=
    tendsto_physicalPowerCorrectionRowError_mul_logL_zero
      epsilon G W hepsilon0 hG hepsilonRate
  have hdensityEvent :=
    GuardSquarefreeErrorRate.eventually_guarded_rawCell_endpoint_density
      P I Cprom Cbank ledger
  have hepsilonT : Tendsto (fun n : ℕ ↦ 8 * epsilon n)
      atTop (nhds 0) := by
    have hLTop : Tendsto Scale.L atTop atTop := by
      simpa only [Scale.L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hInv : Tendsto (fun n : ℕ ↦ (Scale.L n)⁻¹)
        atTop (nhds 0) := tendsto_inv_atTop_zero.comp hLTop
    have hconst : Tendsto
        (fun _n : ℕ ↦ 8 * (Aphys * Real.log Cmax)) atTop
          (nhds (8 * (Aphys * Real.log Cmax))) := tendsto_const_nhds
    have hmul := hconst.mul hInv
    apply (show Tendsto (fun n : ℕ ↦
        (8 * (Aphys * Real.log Cmax)) * (Scale.L n)⁻¹)
        atTop (nhds 0) by simpa only [mul_zero] using hmul).congr'
    filter_upwards with n
    dsimp only [epsilon, canonicalPhysicalPowerCorrectionEpsilon]
    rw [div_eq_mul_inv]
    ring
  have hsmallEvent : ∀ᶠ n : ℕ in atTop, 8 * epsilon n ≤ 1 :=
    hepsilonT.eventually (eventually_le_nhds (by norm_num))
  obtain ⟨Ndensity, hNdensity⟩ := Filter.eventually_atTop.1 hdensityEvent
  obtain ⟨Nsmall, hNsmall⟩ := Filter.eventually_atTop.1 hsmallEvent
  refine ⟨hG, hrowRate, max Ndensity Nsmall, ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW hsep hremaining
    hcanonical heta hphys p
  have hNdensity' : Ndensity ≤ B.sampleData.n :=
    (Nat.le_max_left _ _).trans hN
  have hNsmall' : Nsmall ≤ B.sampleData.n :=
    (Nat.le_max_right _ _).trans hN
  have hdensity := hNdensity B.sampleData.n hNdensity'
  have hsmall : 8 * epsilon B.sampleData.n ≤ 1 :=
    hNsmall B.sampleData.n hNsmall'
  have hWBridge : 1 < B.sampleData.W := by
    simpa only [hBW] using hW
  have hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhiC : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound Cmax B.sampleData.n := by
    intro sigma
    rw [hhi sigma]
    exact FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperMax sigma) B.sampleData.n
  have hrho (c : Cell Head) :
      0 < canonicalPhysicalCellDensity P I c :=
    canonicalPhysicalCellDensity_pos P I c
  have hcard (c : Cell Head) :
      canonicalPhysicalCellDensity P I c *
          (B.sampleData.hi c.2 : ℝ) ≤
        ((B.sampleData.cellFinset c).card : ℝ) := by
    have hc := (hdensity c).2
    rw [hcanonical]
    simpa only [canonicalPhysicalCellDensity,
      canonicalSampleData_hi, canonicalSampleData_cellFinset] using hc
  have hKphys : ∀ c (m : B.sampleData.SampleAt c),
      |B.physicalScore ⟨c, m⟩| ≤ Real.log Cmax := by
    intro c m
    exact B.abs_physicalScore_le_log_upperBound I hlowerOne hupperMax
      hlo hhi ⟨c, m⟩
  have hGdom : ∀ c,
      Real.exp (2 * ((Acoef / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)))) /
          canonicalPhysicalCellDensity P I c ≤ G := by
    intro c
    let K := Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W
    have hexponent :
        (Acoef / B.L) *
            (Real.log (B.sampleData.hi c.2 : ℝ) /
              Real.log (B.sampleData.W : ℝ)) ≤ K := by
      simpa only [K, hBW] using
        B.mediumFallbackExponent_le c hCmax hWBridge hAcoef (hhiC c.2)
    have hcell :
        Real.exp (2 * ((Acoef / B.L) *
            (Real.log (B.sampleData.hi c.2 : ℝ) /
              Real.log (B.sampleData.W : ℝ)))) /
              canonicalPhysicalCellDensity P I c ≤
          Real.exp (2 * K) /
              canonicalPhysicalCellDensity P I c := by
      exact div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hexponent (by norm_num)))
        (hrho c).le
    have hsum : Real.exp (2 * K) /
          canonicalPhysicalCellDensity P I c ≤ G := by
      dsimp only [G, canonicalPhysicalPowerCorrectionConstant]
      exact Finset.single_le_sum
        (fun d _ ↦ div_nonneg (Real.exp_pos _).le (hrho d).le)
        (Finset.mem_univ c)
    exact hcell.trans hsum
  exact B.actual_powerCorrection_physicalMedium_weightedRow_le
    xi (canonicalPhysicalCellDensity P I)
      hAcoef hAphys0 hlogC0 hG hWBridge hrho hcard heta hphys hKphys
        hsmall hGdom p

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution : Erdos390.RemainingAnalyticGoal002_001.{u_1, u_2} := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.exists_eventually_canonicalPhysical_powerCorrection_row
