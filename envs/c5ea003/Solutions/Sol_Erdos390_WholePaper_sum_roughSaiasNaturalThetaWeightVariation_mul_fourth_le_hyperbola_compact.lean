-- Prove2me | solution 1 for Erdos390.WholePaper.sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_hyperbola_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:51:27.868689+00:00
-- url     : https://prove2.me/submissions/28598af7-e7a9-4f31-bc8f-63c35b700d32

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Theorems.Thm_Erdos390_WholePaper_roughSaiasBaseFreeFractionalIntegral_hyperbola_sum_abs_succ_sub_le_two_inv_log_compact
import Theorems.Thm_Erdos390_WholePaper_roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_hyperbolaComponents_compact
import Theorems.Thm_Erdos390_WholePaper_sum_roughSaiasSelectorCellLedger_mul_fourth_le_compact




section
theorem Erdos390.WholePaper.sum_roughSaiasSelectorCellLedger_mul_fourth_le : Erdos390.RemainingAnalyticGoal008_037 := @Erdos390.WholePaper.sum_roughSaiasSelectorCellLedger_mul_fourth_le_compact
end
section
theorem Erdos390.WholePaper.roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_hyperbolaComponents : Erdos390.RemainingAnalyticGoal008_030 := @Erdos390.WholePaper.roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_hyperbolaComponents_compact
end
section
theorem Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral_hyperbola_sum_abs_succ_sub_le_two_inv_log : Erdos390.RemainingAnalyticGoal008_024 := @Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral_hyperbola_sum_abs_succ_sub_le_two_inv_log_compact
end
/- Source module: Erdos390.WholePaper.RoughSaiasNormalization -/
section


/-!
# The finite de Bruijn--Saias normal form on the five Dickman faces

Section 8.5 of the paper uses the integration-by-parts identity

`Lambda(z,y) = z * G_y(log z / log y) - fract z`,

where

`G_y(u) = rho(u) - integral rho'(u-v) * fract(y^v) * y^(-v) dv`.

This file formalizes the finite normal form, its exact initial face, the
compact bounded-variation datum behind the asserted Lipschitz estimate, and
the exact way in which this normalization enters the already isolated rough
prime-transition ledger.

The cited Hildebrand--Tenenbaum--Saias estimate for `Psi - Lambda` is not
proved in the paper.  Accordingly, no theorem below declares that estimate
as an axiom.  Its precise endpoint-shaped consequence is exposed as a `Prop`
which can be passed to a reduction theorem.  In particular, the endpoint
error remains proportional to `A+B`, not to the short gap `B-A`.
-/

open scoped BigOperators Interval ENNReal

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The finite `G_y` normal form -/









































/-! ## The bounded-variation datum and compact Lipschitz reduction -/

/-- The finite Dickman function is antitone on the whole nonnegative compact
range.  The existing library theorem starts at `1`; the initial interval is
filled in here using the exact constant branch. -/
theorem roughRho_antitoneOn_zero_five :
    AntitoneOn rho (Icc (0 : ℝ) 5) := by
  intro a ha b hb hab
  by_cases hb1 : b ≤ 1
  · rw [rho_eq_one_of_le_one hb1,
      rho_eq_one_of_le_one (hab.trans hb1)]
  by_cases ha1 : 1 ≤ a
  · exact antitoneOn_rho_one_five
      ⟨ha1, ha.2⟩ ⟨(le_of_not_ge hb1), hb.2⟩ hab
  · rw [rho_eq_one_of_le_one (le_of_not_ge ha1)]
    exact FriableAsymptotic.rho_le_one_of_le_five hb.2



















/-! ## The explicit `1 / log y` normalization correction -/











/-! ## Exact connection to the genuine friable residual -/























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasBaseChange -/
section


/-!
# Base-free sawtooth coordinates for the Saias correction

The difficult base variation in `roughSaiasG m` contains
`fract(m^v) * m^(-v)`.  This file records the exact substitution `t=m^v`
before any absolute value is taken.  After multiplication by the Jacobian,
the sawtooth is `fract(t)`, independent of `m`; all base dependence is left
in the logarithmic Dickman kernel and the factor `1 / log m`.

This is an exact identity for the finite `[0,5]` integral.  The one-variable
Jacobian theorem is used because its monotone form permits the discontinuous
fractional-part integrand.
-/

open scoped Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section







/-- The transformed coordinate is a single log difference divided by the
base logarithm. -/
theorem roughSaiasBaseFreeDickmanCoordinate_eq_sub_div
    (q m : ℕ) (t : ℝ) :
    roughSaiasBaseFreeDickmanCoordinate q m t =
      (Real.log (q : ℝ) - Real.log t) / Real.log (m : ℝ) := by
  unfold roughSaiasBaseFreeDickmanCoordinate
  ring









































/-! ## Exact floor/base pairing in the transformed coordinate -/











/-! ## The signed center as a base-free quotient-block sum -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpVariation -/
section


/-!
# Sharp active-face variation of the base-free Saias kernel

On the active Dickman faces the apparently competing changes in the
Dickman coordinate and in `1 / log m` cancel algebraically.  If

`u_m(t) = (log q - log t) / log m`,

then

`rho'(u_m(t)) / log m = -rho (u_m(t) - 1) / (log q - log t)`.

The denominator on the right is independent of `m`.  Consequently, while
`t <= q / m` and the coordinates remain on the five constructed faces, the
scaled kernel is antitone as the base increases.  Its absolute consecutive
variation on an all-active finite block therefore telescopes exactly.  No
triangle inequality between the coordinate and coefficient changes is used.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

































/-- The global five-face hypothesis at the first base propagates to every
natural hyperbola quotient and every sawtooth variable `t ≥ 1`. -/
theorem roughSaiasBaseFreeDickmanCoordinate_natHyperbola_le_five
    {X a m : ℕ} (ha2 : 2 ≤ a) (ham : a ≤ m) (hmX : m ≤ X)
    {t : ℝ} (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5 := by
  have hm2 : 2 ≤ m := ha2.trans ham
  have hmposNat : 0 < m := by omega
  have hqpos : 0 < X / m := Nat.div_pos hmX hmposNat
  have hqX : X / m ≤ X := Nat.div_le_self X m
  have hapos : 0 < (a : ℝ) := by positivity
  have hqposR : 0 < ((X / m : ℕ) : ℝ) := by exact_mod_cast hqpos
  have hXposR : 0 < (X : ℝ) := by exact_mod_cast (hmposNat.trans_le hmX)
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlogqX : Real.log ((X / m : ℕ) : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hqposR (by exact_mod_cast hqX)
  have hlogam : Real.log (a : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hapos (by exact_mod_cast ham)
  rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
  calc
    (Real.log ((X / m : ℕ) : ℝ) - Real.log t) /
          Real.log (m : ℝ) ≤
        Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hlogm.le
    _ ≤ Real.log (X : ℝ) / Real.log (m : ℝ) :=
      div_le_div_of_nonneg_right hlogqX hlogm.le
    _ ≤ Real.log (X : ℝ) / Real.log (a : ℝ) :=
      div_le_div_of_nonneg_left hlogX0 hloga hlogam
    _ ≤ 5 := hu5



/-- Log-ratio form of five-face propagation along natural hyperbola
quotients. -/
theorem roughSaiasNatHyperbolaLogRatio_le_five
    {X a m : ℕ} (ha2 : 2 ≤ a) (ham : a ≤ m) (hmX : m ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5 := by
  simpa [roughSaiasBaseFreeDickmanCoordinate] using
    (roughSaiasBaseFreeDickmanCoordinate_natHyperbola_le_five
      ha2 ham hmX (t := (1 : ℝ)) (by norm_num) hu5)





/-- The Dickman coordinate at `t = 1` is antitone along the natural
hyperbola path. -/
theorem roughSaiasNatHyperbolaLogRatio_succ_le
    {X m : ℕ} (hm2 : 2 ≤ m) (hnextX : m + 1 ≤ X) :
    Real.log ((X / (m + 1) : ℕ) : ℝ) /
        Real.log ((m + 1 : ℕ) : ℝ) ≤
      Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) := by
  have hmPos : 0 < m := by omega
  have hnextPos : 0 < m + 1 := by omega
  have hqNext : 1 ≤ X / (m + 1) := Nat.div_pos hnextX hnextPos
  have hqLe : X / (m + 1) ≤ X / m :=
    Nat.div_le_div_left (a := X) (Nat.le_succ m) hmPos
  have hqNextPosR : 0 < ((X / (m + 1) : ℕ) : ℝ) := by positivity
  have hqNowOne : 1 ≤ X / m := hqNext.trans hqLe
  have hlogqNow0 : 0 ≤ Real.log ((X / m : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hqNowOne)
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogmLe : Real.log (m : ℝ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_succ m))
  have hlogqLe : Real.log ((X / (m + 1) : ℕ) : ℝ) ≤
      Real.log ((X / m : ℕ) : ℝ) :=
    Real.log_le_log hqNextPosR (by exact_mod_cast hqLe)
  calc
    Real.log ((X / (m + 1) : ℕ) : ℝ) /
          Real.log ((m + 1 : ℕ) : ℝ) ≤
        Real.log ((X / m : ℕ) : ℝ) /
          Real.log ((m + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hlogqLe (by positivity)
    _ ≤ Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) :=
      div_le_div_of_nonneg_left hlogqNow0 hlogm hlogmLe

/-- The rho component has total hyperbola-path variation at most one. -/
theorem sum_abs_rho_natHyperbolaLogRatio_succ_sub_le_one
    {X a b : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
              Real.log ((m + 1 : ℕ) : ℝ)) -
          rho (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ))|) ≤
      1 := by
  have hmono : ∀ m ∈ Finset.Ico a b,
      rho (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ)) ≤
        rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
          Real.log ((m + 1 : ℕ) : ℝ)) := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hm2 : 2 ≤ m := ha2.trans hmData.1
    have hnextX : m + 1 ≤ X := by omega
    have hqNow : 1 ≤ X / m := Nat.div_pos (by omega) (by omega)
    have hqNext : 1 ≤ X / (m + 1) := Nat.div_pos hnextX (by omega)
    have huNow0 : 0 ≤ Real.log ((X / m : ℕ) : ℝ) /
        Real.log (m : ℝ) :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast hqNow)) (by positivity)
    have huNext0 : 0 ≤ Real.log ((X / (m + 1) : ℕ) : ℝ) /
        Real.log ((m + 1 : ℕ) : ℝ) :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast hqNext)) (by positivity)
    have huNow5 := roughSaiasNatHyperbolaLogRatio_le_five
      ha2 hmData.1 (by omega) hu5
    have huNext5 := roughSaiasNatHyperbolaLogRatio_le_five (m := m + 1)
      ha2 (by omega) (by omega) hu5
    exact roughRho_antitoneOn_zero_five
      ⟨huNext0, huNext5⟩ ⟨huNow0, huNow5⟩
      (roughSaiasNatHyperbolaLogRatio_succ_le hm2 hnextX)
  have htelescope :
      (∑ m ∈ Finset.Ico a b,
          |rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
                Real.log ((m + 1 : ℕ) : ℝ)) -
            rho (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ))|) =
        rho (Real.log ((X / b : ℕ) : ℝ) / Real.log (b : ℝ)) -
          rho (Real.log ((X / a : ℕ) : ℝ) / Real.log (a : ℝ)) := by
    calc
      (∑ m ∈ Finset.Ico a b,
          |rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
                Real.log ((m + 1 : ℕ) : ℝ)) -
            rho (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ))|) =
        ∑ m ∈ Finset.Ico a b,
          (rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
                Real.log ((m + 1 : ℕ) : ℝ)) -
            rho (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ))) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [abs_of_nonneg (sub_nonneg.mpr (hmono m hm))]
      _ = rho (Real.log ((X / b : ℕ) : ℝ) / Real.log (b : ℝ)) -
          rho (Real.log ((X / a : ℕ) : ℝ) / Real.log (a : ℝ)) := by
        clear hmono hbX
        induction b, hab using Nat.le_induction with
        | base => simp
        | succ b hab ih =>
            rw [Finset.sum_Ico_succ_top hab, ih]
            ring
  have haX : a ≤ X := hab.trans hbX
  have hqA : 1 ≤ X / a := Nat.div_pos haX (by omega)
  have hqB : 1 ≤ X / b := Nat.div_pos hbX (by omega)
  have huA0 : 0 ≤ Real.log ((X / a : ℕ) : ℝ) / Real.log (a : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hqA)) (by positivity)
  have huB0 : 0 ≤ Real.log ((X / b : ℕ) : ℝ) / Real.log (b : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hqB)) (by positivity)
  have huA5 := roughSaiasNatHyperbolaLogRatio_le_five
    ha2 le_rfl haX hu5
  have huB5 := roughSaiasNatHyperbolaLogRatio_le_five
    ha2 hab hbX hu5
  have hrhoA0 : 0 ≤
      rho (Real.log ((X / a : ℕ) : ℝ) / Real.log (a : ℝ)) :=
    (rho_pos_on_zero_five huA0 huA5).le
  have hrhoB1 :
      rho (Real.log ((X / b : ℕ) : ℝ) / Real.log (b : ℝ)) ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five huB5
  rw [htelescope]
  linarith



/-! ## The genuinely real hyperbola path inside natural cells -/



























































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpCorrectionTarget -/
section


/-!
# The sharp fully real correction target

The reverse defect splits directly into:

1. the ordinary Dickman continuous-integral versus prime-theta
   discrepancy, already closed by the existing Riemann and fourth-power
   PNT estimates; and
2. one fully real Saias correction integral versus its matching residual
   prime weight.

This is the minimal analytic target left after all exact base changes,
floor pairings, upper-selector cells, and standard Dickman estimates have
been discharged.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section



































/-! ## Closing the lower fully-real quadrature -/

























/-- Fourth-power weighted variation of the natural theta weight on an
arbitrary hyperbola block.  This is the lower-face counterpart of the
selector estimate: coefficient drift uses the same selector ledger, while
rho and fractional-integral variations telescope globally. -/
theorem sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_hyperbola
    {C : ℝ} (hC : 0 ≤ C) {X a b : ℕ}
    (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      16 * (C * (X : ℝ) * (2 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 5 +
        C * (X : ℝ) * (1 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 6) +
        (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) *
          (1 + 2 / Real.log (a : ℝ)) := by
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hCX : 0 ≤ C * (X : ℝ) := by positivity
  let R : ℕ → ℝ := fun m =>
    |rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
          Real.log ((m + 1 : ℕ) : ℝ)) -
      rho (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ))| +
    |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
      roughSaiasBaseFreeFractionalIntegral (X / m) m|
  have hRnonneg : ∀ m, 0 ≤ R m := fun m =>
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hpoint : ∀ m ∈ Finset.Ico a b,
      |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) ≤
        16 * (roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) +
        (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) * R m := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hm2 : 2 ≤ m := ha2.trans hmData.1
    have hmpos : 0 < (m : ℝ) := by positivity
    have hlogm : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    have hlogam : Real.log (a : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hmData.1)
    have hpow5 : Real.log (a : ℝ) ^ 5 ≤ Real.log (m : ℝ) ^ 5 :=
      pow_le_pow_left₀ hloga.le hlogam 5
    have hcoeff :
        ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ))) *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) =
          C * (X : ℝ) / Real.log (m : ℝ) ^ 5 := by
      field_simp [hmpos.ne', hlogm.ne']
    have hcoeffLe : C * (X : ℝ) / Real.log (m : ℝ) ^ 5 ≤
        C * (X : ℝ) / Real.log (a : ℝ) ^ 5 :=
      div_le_div_of_nonneg_left hCX (pow_pos hloga 5) hpow5
    have hweightNonneg :
        0 ≤ C * ((m : ℝ) / Real.log (m : ℝ) ^ 4) := by positivity
    have hbase :=
      roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_hyperbolaComponents
        ha2 hab hbX hm hu5
    have hmul := mul_le_mul_of_nonneg_right hbase hweightNonneg
    calc
      |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) ≤
        (16 * roughSaiasSelectorCellLedger X m +
          ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ))) * R m) *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) := by
          simpa only [R] using hmul
      _ = 16 * (roughSaiasSelectorCellLedger X m *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) +
          (C * (X : ℝ) / Real.log (m : ℝ) ^ 5) * R m := by
        rw [← hcoeff]
        ring
      _ ≤ 16 * (roughSaiasSelectorCellLedger X m *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) +
          (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) * R m :=
        add_le_add
          le_rfl
          (mul_le_mul_of_nonneg_right hcoeffLe (hRnonneg m))
  have hselector := sum_roughSaiasSelectorCellLedger_mul_fourth_le
    hC X ha2 hab
  have hRsum : (∑ m ∈ Finset.Ico a b, R m) ≤
      1 + 2 / Real.log (a : ℝ) := by
    have hrho := sum_abs_rho_natHyperbolaLogRatio_succ_sub_le_one
      ha2 hab hbX hu5
    have hI :=
      roughSaiasBaseFreeFractionalIntegral_hyperbola_sum_abs_succ_sub_le_two_inv_log
        ha2 hab hbX hu5
    calc
      (∑ m ∈ Finset.Ico a b, R m) =
          (∑ m ∈ Finset.Ico a b,
            |rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
                  Real.log ((m + 1 : ℕ) : ℝ)) -
              rho (Real.log ((X / m : ℕ) : ℝ) /
                Real.log (m : ℝ))|) +
          ∑ m ∈ Finset.Ico a b,
            |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
              roughSaiasBaseFreeFractionalIntegral (X / m) m| := by
        simp only [R, Finset.sum_add_distrib]
      _ ≤ 1 + 2 / Real.log (a : ℝ) := add_le_add hrho hI
  calc
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      ∑ m ∈ Finset.Ico a b,
        (16 * (roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) +
        (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) * R m) :=
      Finset.sum_le_sum hpoint
    _ = 16 * (∑ m ∈ Finset.Ico a b,
          roughSaiasSelectorCellLedger X m *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) +
        (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) *
          (∑ m ∈ Finset.Ico a b, R m) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 16 * (C * (X : ℝ) * (2 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 5 +
        C * (X : ℝ) * (1 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 6) +
        (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) *
          (1 + 2 / Real.log (a : ℝ)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hselector (by norm_num))
        (mul_le_mul_of_nonneg_left hRsum (by positivity))































/-! ## Closed sharp defect and endpoint witnesses -/











end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_035 := by
  exact @Erdos390.WholePaper.sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_hyperbola
