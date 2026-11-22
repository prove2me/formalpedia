-- Prove2me | solution 1 for Erdos390.Full.PaperCanonicalTiltedPrefixRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_tilted_valuation_prefix_rate_unrestricted_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:15:45.98272+00:00
-- url     : https://prove2.me/submissions/a5dbdcc2-085b-4377-aff2-96714892655b

import Definitions.Def_erdos390_remaining_analytic_propositions_004
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
import Theorems.Thm_Erdos390_Full_PaperRawTiltedPrefixRowUnrestricted_exists_uniform_rawCell_tilted_valuation_prefix_rate_unrestricted_compact
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound


section
theorem Erdos390.Full.PaperRawTiltedPrefixRowUnrestricted.exists_uniform_rawCell_tilted_valuation_prefix_rate_unrestricted : Erdos390.RemainingAnalyticGoal004_007 := @Erdos390.Full.PaperRawTiltedPrefixRowUnrestricted.exists_uniform_rawCell_tilted_valuation_prefix_rate_unrestricted_compact
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

/- Source module: Erdos390.Full.FriableAsymptotic -/
section


/-!
# Friable counts on the Erdős 390 scale

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's actual finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace Erdos390.Full.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale

/-! ## Quantitative prime-number input

The finite de Bruijn induction below needs a power-saving prime Stieltjes
estimate.  We derive it here from the audited medium-strength PNT, rather than
postulating a prime-distribution contract.  The exponential PNT remainder is
stronger than every fixed power of `1 / log x`.
-/



















































/-! ## Explicit regularity of the finite Dickman kernel -/









/-! ## The Dickman test weight in the prime recurrence -/



















































/-! ## Explicit oscillation and Riemann error for the Dickman weight -/


open DickmanBasic






























/-! ## Quantitative PNT transfer for the Dickman prime weight

The following estimates combine the preceding Chebyshev--Stieltjes identity,
the audited medium PNT, and the explicit Dickman-weight oscillation bound.
They are the one-prime analytic input for the finite de Bruijn induction.
-/


















/-! ## Uniform floor stability for the recursive Dickman kernel -/






















































/-- The integral cutoff `floor(n^(2/9))` retains enough logarithmic size
for the complete four-mark coordinate range. -/
theorem eventually_one_fifth_L_le_log_yNat :
    ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ) := by
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_gt_atTop 0,
    hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually
      (Filter.eventually_ge_atTop (45 * Real.log 2))] with n hn hyn hLn
  have hypos : 0 < y n := y_pos hn
  have hyNatLower : y n / 2 ≤ (yNat n : ℝ) := by
    have hfloor : y n < (yNat n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) :=
    (div_pos hypos (by norm_num)).trans_le hyNatLower
  have hlogLower : Real.log (y n / 2) ≤ Real.log (yNat n : ℝ) :=
    Real.log_le_log (div_pos hypos (by norm_num)) hyNatLower
  have hlogDiv : Real.log (y n / 2) = Real.log (y n) - Real.log 2 := by
    rw [Real.log_div hypos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  calc
    (1 / 5 : ℝ) * L n ≤ Real.log (y n / 2) := by
      rw [hlogDiv, log_y hn]
      linarith
    _ ≤ Real.log (yNat n : ℝ) := hlogLower






end Erdos390.Full.FriableAsymptotic

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

/- Source module: Erdos390.Full.PrimePowerCovariance -/
section


/-!
# Exact prime-power covariance expansion

This file replaces the algebraic part of the prime-power transfer by proofs
for the actual valuation and divisor indicators under an actual finite
probability law.  In particular, `V = I + J` and all `JI`, `IJ`, and `JJ`
covariances are finite sums of genuine prime-power indicator covariances.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega Iota : Type*} [Fintype Omega]















theorem covariance_zero_right (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    mu.covariance F (fun _ ↦ 0) = 0 := by
  simp [covariance, expect]















end FiniteProbability

namespace PrimePowerCovariance

open ArithmeticModel



namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}













































end BoundedValuationLaw

end PrimePowerCovariance

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.ValuationTiltCell -/
section


/-!
# Actual compact valuation tilts on a finite cell

This file substitutes the genuine valuation score into the omitted-score
comparison.  Both divisor-score moments are discharged by exact
common-multiple counting; no probabilistic independence is assumed.
-/

open scoped BigOperators

namespace Erdos390.Full.ValuationTiltCell

open ArithmeticModel DivisibilityMomentBounds FiniteProbability
open OmittedScoreCell ValuationScoreDomination

noncomputable section





/-- Uniform bound for the genuine compact valuation score using the physical
logarithm rather than the (much larger) number of prime-power columns. -/
theorem abs_valuationScore_le_log_ratio
    (P : Finset ℕ) (eta : ℕ → ℝ) {m M W : ℕ} {B L : ℝ}
    (hm : 0 < m) (hmM : m ≤ M)
    (hW : 1 < W) (hpW : ∀ p ∈ P, W ≤ p)
    (hB : 0 ≤ B) (hL : 0 < L) (heta : ∀ p ∈ P, |eta p| ≤ B) :
    |valuationScore P eta L m| ≤
      (B / L) * (Real.log (M : ℝ) / Real.log (W : ℝ)) := by
  unfold valuationScore
  calc
    |∑ p ∈ P, (eta p / L) * valuation p m| ≤
        ∑ p ∈ P, |(eta p / L) * valuation p m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ P, (|eta p| / L) * valuation p m := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [abs_mul, abs_div, abs_of_pos hL,
        abs_of_nonneg (valuation_nonneg p m)]
    _ ≤ ∑ p ∈ P, (B / L) * valuation p m := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (heta p hp) hL.le)
        (valuation_nonneg p m)
    _ = (B / L) * (∑ p ∈ P, valuation p m) := by
      rw [Finset.mul_sum]
    _ ≤ (B / L) *
        (Real.log (M : ℝ) / Real.log (W : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (sum_valuation_le_log_ratio P hm hmM hW hpW)
        (div_nonneg hB hL.le)



end

end Erdos390.Full.ValuationTiltCell

end

/- Source module: Erdos390.Full.OmittedTiltFallback -/
section


/-!
# Arbitrary-modulus fallback under an omitted valuation tilt

The four-mark theorem gives the sharp Dickman main term.  Terms outside that
chamber only require an upper bound.  This file proves the required fallback
directly: a bounded exponential tilt changes every nonnegative event by at
most its pointwise density-ratio bound, and elementary multiple counting on
an actual positive cell gives the reciprocal divisor scale for every modulus.
-/

namespace Erdos390.Full

open ArithmeticModel DivisibilityMomentBounds

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- The partition function of a score bounded in absolute value by `K` is at
least `exp (-K)`. -/
theorem exp_neg_le_expPartition (mu : FiniteProbability Omega)
    (score : Omega → ℝ) (K : ℝ) (hscore : ∀ omega, |score omega| ≤ K) :
    Real.exp (-K) ≤ mu.expPartition score := by
  unfold expPartition expect
  calc
    Real.exp (-K) = ∑ omega, mu.mass omega * Real.exp (-K) := by
      rw [← Finset.sum_mul, mu.mass_sum, one_mul]
    _ ≤ ∑ omega, mu.mass omega * Real.exp (score omega) := by
      apply Finset.sum_le_sum
      intro omega homega
      apply mul_le_mul_of_nonneg_left _ (mu.mass_nonneg omega)
      exact Real.exp_le_exp.mpr ((neg_le_neg (hscore omega)).trans
        (neg_abs_le (score omega)))

/-- Pointwise bounded tilting changes any nonnegative expectation by at most
the exact density-ratio factor `exp (2K)`. -/
theorem exponentialTilt_expect_le_exp_two_mul
    (mu : FiniteProbability Omega) (A score : Omega → ℝ) (K : ℝ)
    (hA : ∀ omega, 0 ≤ A omega)
    (hscore : ∀ omega, |score omega| ≤ K) :
    (mu.exponentialTilt score).expect A ≤
      Real.exp (2 * K) * mu.expect A := by
  have hZpos : 0 < mu.expPartition score := mu.expPartition_pos score
  have hZlower : Real.exp (-K) ≤ mu.expPartition score :=
    mu.exp_neg_le_expPartition score K hscore
  have hEA0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA
  have hnum0 : 0 ≤ mu.expect (fun omega ↦ A omega * Real.exp (score omega)) :=
    mu.expect_nonneg _ fun omega ↦ mul_nonneg (hA omega) (Real.exp_pos _).le
  have hnum : mu.expect (fun omega ↦ A omega * Real.exp (score omega)) ≤
      Real.exp K * mu.expect A := by
    unfold expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro omega homega
    calc
      mu.mass omega * (A omega * Real.exp (score omega)) ≤
          mu.mass omega * (A omega * Real.exp K) := by
        apply mul_le_mul_of_nonneg_left _ (mu.mass_nonneg omega)
        apply mul_le_mul_of_nonneg_left _ (hA omega)
        exact Real.exp_le_exp.mpr ((le_abs_self (score omega)).trans
          (hscore omega))
      _ = Real.exp K * (mu.mass omega * A omega) := by ring
  have hinv : (mu.expPartition score)⁻¹ ≤ Real.exp K := by
    apply (inv_le_iff_one_le_mul₀ hZpos).2
    calc
      1 = Real.exp K * Real.exp (-K) := by
        rw [← Real.exp_add]
        ring_nf
        simp
      _ ≤ Real.exp K * mu.expPartition score :=
        mul_le_mul_of_nonneg_left hZlower (Real.exp_pos K).le
  rw [mu.exponentialTilt_expect_eq A score, div_eq_mul_inv]
  calc
    mu.expect (fun omega ↦ A omega * Real.exp (score omega)) *
        (mu.expPartition score)⁻¹ ≤
      (Real.exp K * mu.expect A) * (mu.expPartition score)⁻¹ :=
        mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hZpos.le)
    _ ≤ (Real.exp K * mu.expect A) * Real.exp K :=
      mul_le_mul_of_nonneg_left hinv
        (mul_nonneg (Real.exp_pos K).le hEA0)
    _ = Real.exp (2 * K) * mu.expect A := by
      rw [show Real.exp (2 * K) = Real.exp K * Real.exp K by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring

end FiniteProbability

namespace OmittedTiltFallback

open FiniteProbability ValuationScoreDomination ValuationTiltCell





end OmittedTiltFallback

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.GuardDeletionProbability -/
section


/-!
# Exact perturbation bounds for deleting a finite guard set

This module contains the finite-probability algebra used by the guarded-cell
corollary after the arithmetic guard census supplies a cardinality bound.
Deletion is defined on the original finite sample type (guarded points receive
mass zero) and is normalized exactly.  The expectation and covariance losses
are proved from the deleted mass; they are not stored in a certificate.
-/

open scoped BigOperators

namespace Erdos390.Full
namespace FiniteProbability

noncomputable section

variable {Omega : Type*} [Fintype Omega] [DecidableEq Omega]



omit [DecidableEq Omega] in
theorem guardMass_nonneg (mu : FiniteProbability Omega) (G : Finset Omega) :
    0 ≤ mu.guardMass G :=
  Finset.sum_nonneg fun x _ => mu.mass_nonneg x



/- A guard census and a point-mass bound give the deleted-mass bound used in
the marked-cell application.  This is an inequality for the actual deleted
set, rather than a total-variation hypothesis stored in a certificate. -/


/-- A bounded exponential tilt enlarges every individual atom by at most
the exact density-ratio factor `exp (2K)`. -/
theorem exponentialTilt_mass_le_exp_two_mul
    (mu : FiniteProbability Omega) (score : Omega → ℝ) (K : ℝ)
    (hscore : ∀ x, |score x| ≤ K) (x : Omega) :
    (mu.exponentialTilt score).mass x ≤ Real.exp (2 * K) * mu.mass x := by
  have h := mu.exponentialTilt_expect_le_exp_two_mul
    (fun y : Omega => if y = x then 1 else 0) score K
    (fun y => by by_cases hy : y = x <;> simp [hy]) hscore
  simpa [expect] using h

/-- The same density-ratio estimate summed over the actual guard set. -/
theorem exponentialTilt_guardMass_le_exp_two_mul
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (score : Omega → ℝ) (K : ℝ) (hscore : ∀ x, |score x| ≤ K) :
    (mu.exponentialTilt score).guardMass G ≤
      Real.exp (2 * K) * mu.guardMass G := by
  unfold guardMass
  calc
    (∑ x ∈ G, (mu.exponentialTilt score).mass x) ≤
        ∑ x ∈ G, Real.exp (2 * K) * mu.mass x :=
      Finset.sum_le_sum fun x hx =>
        mu.exponentialTilt_mass_le_exp_two_mul score K hscore x
    _ = Real.exp (2 * K) * ∑ x ∈ G, mu.mass x := by
      rw [Finset.mul_sum]













/-- Exact expectation formula after guard deletion. -/
theorem deleteGuards_expect
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1) (F : Omega → ℝ) :
    (mu.deleteGuards G hsmall).expect F =
      (mu.expect F - mu.guardMoment G F) / (1 - mu.guardMass G) := by
  unfold expect guardMoment
  have hsplit := Finset.sum_sdiff (Finset.subset_univ G)
    (f := fun x => mu.mass x * F x)
  change (∑ x, (if x ∈ G then 0 else
      mu.mass x / (1 - mu.guardMass G)) * F x) = _
  calc
    (∑ x, (if x ∈ G then 0 else
        mu.mass x / (1 - mu.guardMass G)) * F x) =
        ∑ x ∈ (Finset.univ \ G),
          (mu.mass x * F x) / (1 - mu.guardMass G) := by
      rw [Finset.sdiff_eq_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxG : x ∈ G
      · simp [hxG]
      · simp [hxG]
        ring
    _ = (∑ x ∈ (Finset.univ \ G), mu.mass x * F x) /
        (1 - mu.guardMass G) := by rw [Finset.sum_div]
    _ = ((∑ x, mu.mass x * F x) -
          ∑ x ∈ G, mu.mass x * F x) /
        (1 - mu.guardMass G) := by
      congr 1
      linarith



omit [DecidableEq Omega] in
theorem guardPerturbation_nonneg
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1) :
    0 ≤ mu.guardPerturbation G := by
  unfold guardPerturbation
  exact div_nonneg (mul_nonneg (by norm_num) (mu.guardMass_nonneg G))
    (sub_pos.mpr hsmall).le

/- On the paper's small-deletion regime, the exact renormalization loss is
at most four times the deleted probability mass. -/
omit [DecidableEq Omega] in
theorem guardPerturbation_le_four_mul_guardMass
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hhalf : mu.guardMass G ≤ (1 : ℝ) / 2) :
    mu.guardPerturbation G ≤ 4 * mu.guardMass G := by
  let delta := mu.guardMass G
  have hdelta0 : 0 ≤ delta := mu.guardMass_nonneg G
  have hden : 0 < 1 - delta := by
    dsimp only [delta] at hhalf ⊢
    linarith
  unfold guardPerturbation
  dsimp only [delta] at hdelta0 hden ⊢
  rw [div_le_iff₀ hden]
  nlinarith

omit [DecidableEq Omega] in
/- Absolute expectation under a finite probability is bounded by any
pointwise absolute envelope. -/
theorem abs_expect_le_of_abs_le
    (mu : FiniteProbability Omega) (F : Omega → ℝ) {K : ℝ}
    (_hK : 0 ≤ K) (hF : ∀ x, |F x| ≤ K) :
    |mu.expect F| ≤ K := by
  unfold expect
  calc
    |∑ x, mu.mass x * F x| ≤
        ∑ x, |mu.mass x * F x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, mu.mass x * |F x| := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [abs_mul, abs_of_nonneg (mu.mass_nonneg x)]
    _ ≤ ∑ x, mu.mass x * K := by
      exact Finset.sum_le_sum fun x hx =>
        mul_le_mul_of_nonneg_left (hF x) (mu.mass_nonneg x)
    _ = K := by rw [← Finset.sum_mul, mu.mass_sum, one_mul]

omit [DecidableEq Omega] in
theorem abs_guardMoment_le
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (F : Omega → ℝ) {K : ℝ} (_hK : 0 ≤ K)
    (hF : ∀ x, |F x| ≤ K) :
    |mu.guardMoment G F| ≤ mu.guardMass G * K := by
  unfold guardMoment guardMass
  calc
    |∑ x ∈ G, mu.mass x * F x| ≤
        ∑ x ∈ G, |mu.mass x * F x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x ∈ G, mu.mass x * |F x| := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [abs_mul, abs_of_nonneg (mu.mass_nonneg x)]
    _ ≤ ∑ x ∈ G, mu.mass x * K := by
      exact Finset.sum_le_sum fun x hx =>
        mul_le_mul_of_nonneg_left (hF x) (mu.mass_nonneg x)
    _ = (∑ x ∈ G, mu.mass x) * K := by rw [Finset.sum_mul]

/-- Quantitative expectation perturbation after deleting guards. -/
theorem abs_deleteGuards_expect_sub_le
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1)
    (F : Omega → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ x, |F x| ≤ K) :
    |(mu.deleteGuards G hsmall).expect F - mu.expect F| ≤
      K * mu.guardPerturbation G := by
  let delta := mu.guardMass G
  let E := mu.expect F
  let R := mu.guardMoment G F
  have hdelta0 : 0 ≤ delta := mu.guardMass_nonneg G
  have hden : 0 < 1 - delta := sub_pos.mpr hsmall
  have hE : |E| ≤ K := mu.abs_expect_le_of_abs_le F hK hF
  have hR : |R| ≤ delta * K := by
    simpa only [delta, R] using mu.abs_guardMoment_le G F hK hF
  rw [mu.deleteGuards_expect G hsmall F]
  have hre : (E - R) / (1 - delta) - E =
      (delta * E - R) / (1 - delta) := by
    field_simp [ne_of_gt hden]
    ring
  change |(E - R) / (1 - delta) - E| ≤ _
  rw [hre, abs_div, abs_of_pos hden]
  calc
    |delta * E - R| / (1 - delta) ≤
        (delta * |E| + |R|) / (1 - delta) := by
      apply div_le_div_of_nonneg_right _ hden.le
      calc
        |delta * E - R| ≤ |delta * E| + |R| := abs_sub _ _
        _ = delta * |E| + |R| := by
          rw [abs_mul, abs_of_nonneg hdelta0]
    _ ≤ (delta * K + delta * K) / (1 - delta) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact add_le_add
        (mul_le_mul_of_nonneg_left hE hdelta0) hR
    _ = K * mu.guardPerturbation G := by
      unfold guardPerturbation
      dsimp only [delta]
      ring

/-- Covariance perturbation for two pointwise bounded statistics. -/
theorem abs_deleteGuards_covariance_sub_le
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1)
    (F H : Omega → ℝ) {KF KH : ℝ}
    (hKF : 0 ≤ KF) (hKH : 0 ≤ KH)
    (hF : ∀ x, |F x| ≤ KF) (hH : ∀ x, |H x| ≤ KH) :
    |(mu.deleteGuards G hsmall).covariance F H - mu.covariance F H| ≤
      3 * KF * KH * mu.guardPerturbation G := by
  let nu := mu.deleteGuards G hsmall
  let d := mu.guardPerturbation G
  have hd0 : 0 ≤ d := mu.guardPerturbation_nonneg G hsmall
  have hFH : ∀ x, |F x * H x| ≤ KF * KH := by
    intro x
    rw [abs_mul]
    exact mul_le_mul (hF x) (hH x) (abs_nonneg _) hKF
  have hKprod : 0 ≤ KF * KH := mul_nonneg hKF hKH
  have hprodDiff : |nu.expect (fun x => F x * H x) -
      mu.expect (fun x => F x * H x)| ≤ (KF * KH) * d := by
    simpa only [nu, d] using
      mu.abs_deleteGuards_expect_sub_le G hsmall
        (fun x => F x * H x) hKprod hFH
  have hFDiff : |nu.expect F - mu.expect F| ≤ KF * d := by
    simpa only [nu, d] using
      mu.abs_deleteGuards_expect_sub_le G hsmall F hKF hF
  have hHDiff : |nu.expect H - mu.expect H| ≤ KH * d := by
    simpa only [nu, d] using
      mu.abs_deleteGuards_expect_sub_le G hsmall H hKH hH
  have hmuF : |mu.expect F| ≤ KF := mu.abs_expect_le_of_abs_le F hKF hF
  have hnuH : |nu.expect H| ≤ KH := nu.abs_expect_le_of_abs_le H hKH hH
  have hmeanFirst :
      |(nu.expect F - mu.expect F) * nu.expect H| ≤
        (KF * d) * KH := by
    rw [abs_mul]
    exact mul_le_mul hFDiff hnuH (abs_nonneg _)
      (mul_nonneg hKF hd0)
  have hmeanSecond :
      |mu.expect F * (nu.expect H - mu.expect H)| ≤
        KF * (KH * d) := by
    rw [abs_mul]
    exact mul_le_mul hmuF hHDiff (abs_nonneg _) hKF
  unfold covariance
  have hmeanIdentity :
      nu.expect F * nu.expect H - mu.expect F * mu.expect H =
        (nu.expect F - mu.expect F) * nu.expect H +
          mu.expect F * (nu.expect H - mu.expect H) := by ring
  rw [show
    (nu.expect (fun x => F x * H x) - nu.expect F * nu.expect H) -
      (mu.expect (fun x => F x * H x) - mu.expect F * mu.expect H) =
      (nu.expect (fun x => F x * H x) -
        mu.expect (fun x => F x * H x)) -
      (nu.expect F * nu.expect H - mu.expect F * mu.expect H) by ring,
    hmeanIdentity]
  calc
    |(nu.expect (fun x => F x * H x) -
          mu.expect (fun x => F x * H x)) -
        ((nu.expect F - mu.expect F) * nu.expect H +
          mu.expect F * (nu.expect H - mu.expect H))| ≤
        |nu.expect (fun x => F x * H x) -
          mu.expect (fun x => F x * H x)| +
        |(nu.expect F - mu.expect F) * nu.expect H| +
        |mu.expect F * (nu.expect H - mu.expect H)| := by
      calc
        |(nu.expect (fun x => F x * H x) -
              mu.expect (fun x => F x * H x)) -
            ((nu.expect F - mu.expect F) * nu.expect H +
              mu.expect F * (nu.expect H - mu.expect H))| ≤
            |nu.expect (fun x => F x * H x) -
              mu.expect (fun x => F x * H x)| +
            |(nu.expect F - mu.expect F) * nu.expect H +
              mu.expect F * (nu.expect H - mu.expect H)| := abs_sub _ _
        _ ≤ |nu.expect (fun x => F x * H x) -
              mu.expect (fun x => F x * H x)| +
            (|(nu.expect F - mu.expect F) * nu.expect H| +
              |mu.expect F * (nu.expect H - mu.expect H)|) :=
          add_le_add_right (abs_add_le _ _) _
        _ = _ := by ring
    _ ≤ (KF * KH) * d + (KF * d) * KH + KF * (KH * d) := by
      exact add_le_add (add_le_add hprodDiff hmeanFirst) hmeanSecond
    _ = 3 * KF * KH * mu.guardPerturbation G := by
      dsimp only [d]
      ring

end

end FiniteProbability
end Erdos390.Full

end

/- Source module: Erdos390.Full.GuardedUniformCell -/
section


/-!
# Guard deletion on an actual uniform arithmetic cell

The paper deletes an ambient finite guard set from each structured cell.
This module constructs the literal guard subset of the cell, proves that its
cardinality is no larger than the ambient guard census, and combines that fact
with the bounded-tilt density ratio.  No total-variation or covariance error is
assumed.
-/

namespace Erdos390.Full

open FiniteProbability

noncomputable section

namespace GuardedUniformCell

variable {Alpha : Type*} [DecidableEq Alpha]





/-- The subtype guard census injects into the ambient guard census. -/
theorem card_guardSubtype_le (S G : Finset Alpha) :
    (guardSubtype S G).card ≤ G.card := by
  apply Finset.card_le_card_of_injOn (fun x : S => (x : Alpha))
  · intro x hx
    exact mem_guardSubtype.mp hx
  · intro x hx y hy hxy
    exact Subtype.ext hxy

/-- Exact deleted mass before tilting the uniform cell. -/
theorem uniform_guardMass_eq
    (S G : Finset Alpha) (hS : S.Nonempty) :
    (uniformOnFinset S hS).guardMass (guardSubtype S G) =
      ((guardSubtype S G).card : ℝ) / (S.card : ℝ) := by
  unfold guardMass
  simp only [uniformOnFinset_mass, Finset.sum_const, nsmul_eq_mul]
  ring

/-- A bounded tilt assigns the actual guard subset at most its ambient
cardinality divided by the actual cell cardinality, times `exp (2K)`. -/
theorem tilted_uniform_guardMass_le
    (S G : Finset Alpha) (hS : S.Nonempty)
    (score : S → ℝ) (K : ℝ) (hscore : ∀ x, |score x| ≤ K) :
    ((uniformOnFinset S hS).exponentialTilt score).guardMass
        (guardSubtype S G) ≤
      Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ) := by
  have hScard : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hguardCard : ((guardSubtype S G).card : ℝ) ≤ (G.card : ℝ) := by
    exact_mod_cast card_guardSubtype_le S G
  calc
    ((uniformOnFinset S hS).exponentialTilt score).guardMass
          (guardSubtype S G) ≤
        Real.exp (2 * K) *
          (uniformOnFinset S hS).guardMass (guardSubtype S G) :=
      (uniformOnFinset S hS).exponentialTilt_guardMass_le_exp_two_mul
        (guardSubtype S G) score K hscore
    _ = Real.exp (2 * K) *
          (((guardSubtype S G).card : ℝ) / (S.card : ℝ)) := by
      rw [uniform_guardMass_eq]
    _ ≤ Real.exp (2 * K) * ((G.card : ℝ) / (S.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hguardCard hScard.le)
        (Real.exp_pos _).le
    _ = Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ) := by ring



end GuardedUniformCell

end

end Erdos390.Full

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





/-- On a literal cell, the medium part of the bridge score is the genuine
valuation score used by the structured-cell estimates. -/
theorem sigmaCellScore_scaledMedium_eq_valuationScore [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) :
    sigmaCellScore (B.scaledMediumScore xi) c m =
      valuationScore (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L m := by
  unfold sigmaCellScore scaledMediumScore valuationScore
  have hattach := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p ↦ (B.effectiveNatCoefficient xi p / B.L) * valuation p m)
  rw [← hattach]
  apply Finset.sum_congr rfl
  intro p hp
  rw [B.effectiveNatCoefficient_of_mem xi p.2]
  simp only [StructuredSampleData.value]































end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.GuardDeletionReindexing -/
section


/-!
# Exact reindexing after guard deletion

The guard perturbation lemmas use a probability law on the original cell,
with deleted points assigned mass zero.  The bridge uses the subtype of the
literal guard-deleted finset.  This file proves that these are exactly the
same conditional law after reindexing, including after an exponential tilt.
-/

open scoped BigOperators

namespace Erdos390.Full.GuardedUniformCell

open FiniteProbability

noncomputable section

variable {Alpha : Type*} [DecidableEq Alpha]









/-- A sum over non-guard members of the original subtype is exactly the
corresponding sum over the literal difference finset subtype. -/
theorem sum_complement_guard_eq_sum_remaining
    (S G : Finset Alpha) (F : S → ℝ) :
    ∑ x ∈ ((Finset.univ : Finset S) \ guardSubtype S G), F x =
      ∑ y : ↑(S \ G), F (remainingEmbedding S G y) := by
  rw [Finset.sum_subtype
    (p := fun x : ↑S ↦ x ∉ guardSubtype S G)
    ((Finset.univ : Finset S) \ guardSubtype S G)
    (fun x ↦ by simp)]
  symm
  exact Fintype.sum_equiv (remainingEquiv S G)
    (fun y ↦ F (remainingEmbedding S G y))
    (fun x ↦ F x.1) (fun _ ↦ rfl)



theorem remainingExpSum_pos (S G : Finset Alpha)
    (hR : (S \ G).Nonempty) (score : ↑S → ℝ) :
    0 < remainingExpSum S G score := by
  obtain ⟨a, ha⟩ := hR
  let x : ↑(S \ G) := ⟨a, ha⟩
  unfold remainingExpSum
  exact Finset.sum_pos (fun y hy ↦ Real.exp_pos _) ⟨x, Finset.mem_univ x⟩

/-- Partition function of the uniformly weighted remaining subtype. -/
theorem uniform_remaining_expPartition_eq
    (S G : Finset Alpha) (hR : (S \ G).Nonempty)
    (score : ↑S → ℝ) :
    (uniformOnFinset (S \ G) hR).expPartition
        (fun y ↦ score (remainingEmbedding S G y)) =
      (1 / ((S \ G).card : ℝ)) * remainingExpSum S G score := by
  unfold FiniteProbability.expPartition FiniteProbability.expect
    remainingExpSum
  simp only [uniformOnFinset_mass]
  rw [Finset.mul_sum]

/-- Exact remaining mass of a tilted uniform law, expressed through the
same exponential sum as the literal difference-finset law. -/
theorem one_sub_tilted_guardMass_eq
    (S G : Finset Alpha) (hS : S.Nonempty)
    (score : ↑S → ℝ) :
    1 - ((uniformOnFinset S hS).exponentialTilt score).guardMass
        (guardSubtype S G) =
      (1 / (S.card : ℝ) /
          (uniformOnFinset S hS).expPartition score) *
        remainingExpSum S G score := by
  let mu := (uniformOnFinset S hS).exponentialTilt score
  rw [← mu.sum_mass_complement_guard (guardSubtype S G)]
  rw [sum_complement_guard_eq_sum_remaining]
  unfold mu FiniteProbability.exponentialTilt
  simp only [uniformOnFinset_mass]
  unfold remainingExpSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- Pointwise equality of the conditional tilted mass on every surviving
point and the tilted uniform mass on the literal difference finset. -/
theorem deleteGuards_tilted_uniform_mass_remaining_eq
    (S G : Finset Alpha) (hS : S.Nonempty) (hR : (S \ G).Nonempty)
    (score : ↑S → ℝ)
    (hsmall : ((uniformOnFinset S hS).exponentialTilt score).guardMass
      (guardSubtype S G) < 1)
    (y : ↑(S \ G)) :
    (((uniformOnFinset S hS).exponentialTilt score).deleteGuards
        (guardSubtype S G) hsmall).mass (remainingEmbedding S G y) =
      ((uniformOnFinset (S \ G) hR).exponentialTilt
        (fun z ↦ score (remainingEmbedding S G z))).mass y := by
  rw [FiniteProbability.deleteGuards_mass_of_not_mem _ _ _
    (remainingEmbedding_not_guard S G y)]
  rw [one_sub_tilted_guardMass_eq]
  unfold FiniteProbability.exponentialTilt
  simp only [uniformOnFinset_mass]
  rw [uniform_remaining_expPartition_eq]
  have hScard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  have hRcard : ((S \ G).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hR
  have hZS : (uniformOnFinset S hS).expPartition score ≠ 0 :=
    ne_of_gt ((uniformOnFinset S hS).expPartition_pos score)
  have hA : remainingExpSum S G score ≠ 0 :=
    ne_of_gt (remainingExpSum_pos S G hR score)
  field_simp [hScard, hRcard, hZS, hA]

/-- Exact expectation reindexing between the same two probability laws. -/
theorem deleteGuards_tilted_uniform_expect_remaining_eq
    (S G : Finset Alpha) (hS : S.Nonempty) (hR : (S \ G).Nonempty)
    (score : ↑S → ℝ)
    (hsmall : ((uniformOnFinset S hS).exponentialTilt score).guardMass
      (guardSubtype S G) < 1)
    (F : ↑S → ℝ) :
    (((uniformOnFinset S hS).exponentialTilt score).deleteGuards
        (guardSubtype S G) hsmall).expect F =
      ((uniformOnFinset (S \ G) hR).exponentialTilt
        (fun z ↦ score (remainingEmbedding S G z))).expect
          (fun z ↦ F (remainingEmbedding S G z)) := by
  let mu := ((uniformOnFinset S hS).exponentialTilt score).deleteGuards
    (guardSubtype S G) hsmall
  let nu := (uniformOnFinset (S \ G) hR).exponentialTilt
    (fun z ↦ score (remainingEmbedding S G z))
  have hguard :
      ∑ x ∈ guardSubtype S G, mu.mass x * F x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [FiniteProbability.deleteGuards_mass_of_mem]
    · simp
    · exact hx
  have hsplit := Finset.sum_sdiff
    (Finset.subset_univ (guardSubtype S G))
    (f := fun x ↦ mu.mass x * F x)
  rw [hguard, add_zero] at hsplit
  unfold FiniteProbability.expect
  calc
    (∑ x : ↑S, mu.mass x * F x) =
        ∑ x ∈ ((Finset.univ : Finset S) \ guardSubtype S G),
          mu.mass x * F x := hsplit.symm
    _ = ∑ y : ↑(S \ G),
          mu.mass (remainingEmbedding S G y) *
            F (remainingEmbedding S G y) :=
      sum_complement_guard_eq_sum_remaining S G
        (fun x ↦ mu.mass x * F x)
    _ = ∑ y : ↑(S \ G),
          nu.mass y * F (remainingEmbedding S G y) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [show mu.mass (remainingEmbedding S G y) = nu.mass y by
        exact deleteGuards_tilted_uniform_mass_remaining_eq
          S G hS hR score hsmall y]
    _ = ∑ y : ↑(S \ G),
          nu.mass y * F (remainingEmbedding S G y) := rfl

/-- Exact covariance reindexing. -/
theorem deleteGuards_tilted_uniform_covariance_remaining_eq
    (S G : Finset Alpha) (hS : S.Nonempty) (hR : (S \ G).Nonempty)
    (score : ↑S → ℝ)
    (hsmall : ((uniformOnFinset S hS).exponentialTilt score).guardMass
      (guardSubtype S G) < 1)
    (F H : ↑S → ℝ) :
    (((uniformOnFinset S hS).exponentialTilt score).deleteGuards
        (guardSubtype S G) hsmall).covariance F H =
      ((uniformOnFinset (S \ G) hR).exponentialTilt
        (fun z ↦ score (remainingEmbedding S G z))).covariance
          (fun z ↦ F (remainingEmbedding S G z))
          (fun z ↦ H (remainingEmbedding S G z)) := by
  unfold FiniteProbability.covariance
  rw [deleteGuards_tilted_uniform_expect_remaining_eq
      S G hS hR score hsmall F,
    deleteGuards_tilted_uniform_expect_remaining_eq
      S G hS hR score hsmall H,
    deleteGuards_tilted_uniform_expect_remaining_eq
      S G hS hR score hsmall (fun x ↦ F x * H x)]

end

end Erdos390.Full.GuardedUniformCell

end

/- Source module: Erdos390.Full.GuardDeletionSquarefreeProfiles -/
section


/-!
# Reciprocal signed profiles after guard deletion

For the signed squarefree comparison only divisors `p` and `pq` occur.
Although deleting guards first gives an additive probability error, the
paper census is much smaller than `1/y²`; multiplying by the explicit
`y²` factor therefore restores the required reciprocal scale.  This file
records the exact finite step, including renormalization.
-/

namespace Erdos390.Full.GuardDeletionSquarefreeProfiles

open ArithmeticModel Scale FiniteProbability GuardedUniformCell
open OmittedTiltPairChamber PaperPrimePowerChamberError
open PaperScaleMarkedCell

noncomputable section



theorem guardSquarefreeError_nonneg
    (S G : Finset ℕ) (scoreBound : ℝ) (n : ℕ) :
    0 ≤ guardSquarefreeError S G scoreBound n := by
  unfold guardSquarefreeError
  positivity





end

end Erdos390.Full.GuardDeletionSquarefreeProfiles

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

/-- Uniform valuation envelope on a literal raw physical cell. -/
theorem rawCell_totalBandValuation_le
    {Head : Type*} [Fintype Head]
    (P : Head → Pattern) (Iphys : PhysicalIntervals)
    {n W : ℕ} (hW : 1 < W) (c : PaperBridgeFit.Cell Head)
    (m : rawCell P Iphys n c) :
    (∑ q : BandPrime n W, valuation q.1 (m : ℕ)) ≤
      Real.log (physicalBound (Iphys.upper c.2) n : ℝ) /
        Real.log (W : ℝ) := by
  have hm : 0 < (m : ℕ) := by
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
  have hmM : (m : ℕ) ≤ physicalBound (Iphys.upper c.2) n := by
    exact (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
  have hpW : ∀ q ∈ primeBand n W, W ≤ q := by
    intro q hq
    exact (cutoff_lt_of_mem_primeBand hq).le
  have hraw := sum_valuation_le_log_ratio (primeBand n W) hm hmM hW hpW
  calc
    (∑ q : BandPrime n W, valuation q.1 (m : ℕ)) =
        ∑ q ∈ (primeBand n W).attach, valuation q.1 (m : ℕ) := by
      change (∑ q : primeBand n W, valuation q.1 (m : ℕ)) = _
      rfl
    _ = ∑ q ∈ primeBand n W, valuation q (m : ℕ) :=
      Finset.sum_attach (primeBand n W) (fun q ↦ valuation q (m : ℕ))
    _ ≤ _ := hraw



/-- A single medium-prime valuation is bounded by the total valuation
envelope. -/
theorem rawCell_valuation_le_total
    {Head : Type*} [Fintype Head]
    (P : Head → Pattern) (Iphys : PhysicalIntervals)
    {n W : ℕ} (p : BandPrime n W) (c : PaperBridgeFit.Cell Head)
    (m : rawCell P Iphys n c) :
    valuation p.1 (m : ℕ) ≤
      ∑ q : BandPrime n W, valuation q.1 (m : ℕ) := by
  exact Finset.single_le_sum (fun q hq ↦ valuation_nonneg q.1 (m : ℕ))
    (Finset.mem_univ p)









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

private theorem tendsto_L_sq_div_nat_rpow_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ L n ^ 2 / (n : ℝ) ^ a) atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (2 : ℝ) / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ (2 : ℝ) / (n : ℝ) ^ a)
      atTop (nhds 0) at hnat
  simpa [L, Real.rpow_natCast] using hnat

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

/-- The same error survives the extra moving-low harmonic loss
`log (L n)`. -/
theorem tendsto_censusRatioMajorant_mul_y_sq_mul_logL_zero
    (Cprom Cbank : ℕ) :
    Tendsto (fun n : ℕ ↦
      censusRatioMajorant Cprom Cbank n * y n ^ 2 * Real.log (L n))
      atTop (nhds 0) := by
  let a : ℝ := 1 / 3
  have ha : 0 < a := by norm_num [a]
  have hlog := tendsto_L_div_nat_rpow_zero a ha
  have hlogSq := tendsto_L_sq_div_nat_rpow_zero a ha
  let upper : ℕ → ℝ := fun n ↦
    (Cprom : ℝ) * (L n / (n : ℝ) ^ a) +
      3 * (Cbank : ℝ) *
        (L n ^ 2 / (n : ℝ) ^ a +
          2 * (L n / (n : ℝ) ^ a))
  have hupper : Tendsto upper atTop (nhds 0) := by
    dsimp only [upper]
    simpa only [mul_zero, add_zero] using
      (hlog.const_mul (Cprom : ℝ)).add
        ((hlogSq.add (hlog.const_mul 2)).const_mul (3 * (Cbank : ℝ)))
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ L n :=
    hLTop.eventually (eventually_ge_atTop 1)
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_gt_atTop 0, hLge] with n hn hLn
    rw [census_mul_y_sq_expansion Cprom Cbank n hn]
    exact mul_nonneg (by positivity) (Real.log_nonneg hLn)
  · filter_upwards [eventually_gt_atTop 0, hLge] with n hn hLn
    have hlogL : Real.log (L n) ≤ L n :=
      (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hLn)).trans (by linarith)
    rw [census_mul_y_sq_expansion Cprom Cbank n hn]
    dsimp only [upper, a]
    have hbase0 : 0 ≤
        (Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
          3 * (Cbank : ℝ) *
            (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
              2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ))) := by
      positivity
    calc
      ((Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
            3 * (Cbank : ℝ) *
              (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
                2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ)))) * Real.log (L n) ≤
          ((Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
            3 * (Cbank : ℝ) *
              (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
                2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ)))) * L n :=
        mul_le_mul_of_nonneg_left hlogL hbase0
      _ = (Cprom : ℝ) * (L n / (n : ℝ) ^ (1 / 3 : ℝ)) +
          3 * (Cbank : ℝ) *
            (L n ^ 2 / (n : ℝ) ^ (1 / 3 : ℝ) +
              2 * (L n / (n : ℝ) ^ (1 / 3 : ℝ))) := by ring



theorem tendsto_guardRateMajorant_mul_logL_zero
    (Cprom Cbank : ℕ) (constant : ℝ) :
    Tendsto (fun n : ℕ ↦ constant *
      (censusRatioMajorant Cprom Cbank n * y n ^ 2) * Real.log (L n))
      atTop (nhds 0) := by
  have hc : Tendsto (fun _n : ℕ ↦ constant) atTop (nhds constant) :=
    tendsto_const_nhds
  have h := hc.mul
    (tendsto_censusRatioMajorant_mul_y_sq_mul_logL_zero Cprom Cbank)
  simpa only [mul_zero, mul_assoc] using h

/-- The literal squarefree deletion error of a concrete raw cell is bounded
by the preceding universal vanishing rate. -/
theorem guardSquarefreeError_rawCell_le_rateMajorant
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    {n Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (c : PaperBridgeFit.Cell Head) (hn : 1 ≤ n)
    (hdensity :
      PaperScaleMarkedCell.paperCellDensity (P c.1)
          (I.lower c.2) (I.upper c.2) * (n : ℝ) / 2 ≤
        (rawCell P I n c).card)
    (K : ℝ) :
    guardSquarefreeError (rawCell P I n c) G.guards K n ≤
      (4 * Real.exp (2 * K) /
          PaperScaleMarkedCell.paperCellDensity (P c.1)
            (I.lower c.2) (I.upper c.2)) *
        (censusRatioMajorant Cprom Cbank n * y n ^ 2) := by
  let density := PaperScaleMarkedCell.paperCellDensity (P c.1)
    (I.lower c.2) (I.upper c.2)
  have hdensityPos : 0 < density :=
    PaperScaleMarkedCell.paperCellDensity_pos (P c.1) (I.lower_lt_upper c.2)
  have hratio := guard_card_div_rawCell_le P I G c hn hdensity
  have hratio0 : 0 ≤ (G.guards.card : ℝ) /
      ((rawCell P I n c).card : ℝ) := by positivity
  have hcensus0 : 0 ≤ censusRatioMajorant Cprom Cbank n := by
    unfold censusRatioMajorant
    have hL : 0 ≤ L n := Real.log_nonneg (by exact_mod_cast hn)
    have hnR : 0 ≤ (n : ℝ) := by positivity
    have hcoef : 0 ≤
        (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by positivity
    exact div_nonneg (mul_nonneg hcoef (Scale.y_pos (by omega : 0 < n)).le) hnR
  have hmajor0 : 0 ≤
      2 * censusRatioMajorant Cprom Cbank n / density :=
    div_nonneg (mul_nonneg (by norm_num) hcensus0) hdensityPos.le
  have hyNat : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (Scale.y_pos (by omega : 0 < n)).le
  have hyNat0 : 0 ≤ (yNat n : ℝ) := by positivity
  have hy0 : 0 ≤ y n := (Scale.y_pos (by omega : 0 < n)).le
  have hySq : (yNat n : ℝ) ^ 2 ≤ y n ^ 2 :=
    (sq_le_sq₀ hyNat0 hy0).2 hyNat
  unfold guardSquarefreeError
  rw [show 2 * (Real.exp (2 * K) * (G.guards.card : ℝ) /
        ((rawCell P I n c).card : ℝ)) * (yNat n : ℝ) ^ 2 =
      2 * Real.exp (2 * K) *
        ((G.guards.card : ℝ) / ((rawCell P I n c).card : ℝ)) *
          (yNat n : ℝ) ^ 2 by ring]
  calc
    2 * Real.exp (2 * K) *
          ((G.guards.card : ℝ) / ((rawCell P I n c).card : ℝ)) *
          (yNat n : ℝ) ^ 2 ≤
        2 * Real.exp (2 * K) *
          (2 * censusRatioMajorant Cprom Cbank n / density) *
          (yNat n : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio
          (mul_nonneg (by norm_num) (Real.exp_pos _).le))
        (sq_nonneg _)
    _ ≤ 2 * Real.exp (2 * K) *
          (2 * censusRatioMajorant Cprom Cbank n / density) * y n ^ 2 :=
      mul_le_mul_of_nonneg_left hySq
        (mul_nonneg
          (mul_nonneg (by norm_num) (Real.exp_pos _).le) hmajor0)
    _ = (4 * Real.exp (2 * K) / density) *
          (censusRatioMajorant Cprom Cbank n * y n ^ 2) := by ring
    _ = _ := by rfl

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







theorem canonicalGuardSquarefreeError_nonneg
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : ∀ n, Ledger n Cprom Cbank)
    (K : ℝ) (n : ℕ) :
    0 ≤ canonicalGuardSquarefreeError P I G K n := by
  unfold canonicalGuardSquarefreeError
  exact Finset.sum_nonneg fun c hc ↦
    guardSquarefreeError_nonneg _ _ _ _



/-- The same family error remains negligible after the moving-low harmonic
loss. -/
theorem tendsto_canonicalGuardSquarefreeError_mul_logL_zero
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : ∀ n, Ledger n Cprom Cbank) (K : ℝ) :
    Tendsto (fun n : ℕ ↦
      canonicalGuardSquarefreeError P I G K n * Real.log (L n))
      atTop (nhds 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog0 : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (L n) :=
    (hLTop.eventually (eventually_ge_atTop 1)).mono fun n hn ↦
      Real.log_nonneg hn
  have hcell (c : PaperBridgeFit.Cell Head) : Tendsto
      (fun n : ℕ ↦ guardSquarefreeError
          (rawCell P I n c) (G n).guards K n * Real.log (L n))
        atTop (nhds 0) := by
    let constant := 4 * Real.exp (2 * K) /
      PaperScaleMarkedCell.paperCellDensity (P c.1)
        (I.lower c.2) (I.upper c.2)
    have hupper :=
      tendsto_guardRateMajorant_mul_logL_zero Cprom Cbank constant
    have hdensity := eventually_rawCell_density P I
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards [hlog0] with n hlog
      exact mul_nonneg (guardSquarefreeError_nonneg _ _ _ _) hlog
    · filter_upwards [hdensity, eventually_gt_atTop 0, hlog0]
        with n hdens hn hlog
      have hn1 : 1 ≤ n := by omega
      have hguard := guardSquarefreeError_rawCell_le_rateMajorant
        (Head := Head) P I (G n) c hn1 (hdens c) K
      have hguard' : guardSquarefreeError
          (rawCell P I n c) (G n).guards K n ≤
        constant * (censusRatioMajorant Cprom Cbank n * y n ^ 2) := by
        simpa only [constant] using hguard
      exact mul_le_mul_of_nonneg_right hguard' hlog
  have hsum := tendsto_finset_sum
    (Finset.univ : Finset (PaperBridgeFit.Cell Head))
    (fun c hc ↦ hcell c)
  have hsum0 : Tendsto (fun n : ℕ ↦
      ∑ c : PaperBridgeFit.Cell Head,
        guardSquarefreeError (rawCell P I n c) (G n).guards K n *
          Real.log (L n)) atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using hsum
  apply hsum0.congr'
  filter_upwards with n
  unfold canonicalGuardSquarefreeError
  rw [Finset.sum_mul]

end

end Erdos390.Full.GuardSquarefreeErrorRate

end

/- Source module: Erdos390.Full.PaperPrimePowerTailRate -/
section


/-!
# The elementary `p L / yNat^4` tail rate

The valuation cutoff used in the nuisance estimates is `T = yNat n ^ 4`.
For every active prime `p <= yNat n`, its omitted tail becomes negligible
on the sharp `1 / (p L)` scale because `p L / T -> 0` uniformly in `p`.
-/

open Filter Topology

namespace Erdos390.Full.PaperPrimePowerTailRate

open ArithmeticModel Scale

noncomputable section



/-- The integral smoothness cutoff is eventually at least `n^(1/5)`.
This deliberately uses only the already-proved logarithmic lower bound for
`yNat`; no informal floor comparison is hidden. -/
theorem eventually_rpow_one_fifth_le_yNat :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 / 5 : ℝ) ≤ (yNat n : ℝ) := by
  filter_upwards [FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
    Filter.eventually_gt_atTop 1] with n hlog hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hL : 0 < L n := L_pos hn
  have hlogYpos : 0 < Real.log (yNat n : ℝ) := by
    exact (by positivity : 0 < (1 / 5 : ℝ) * L n).trans_le hlog
  have hYpos : (0 : ℝ) < (yNat n : ℝ) :=
    (Real.log_pos_iff (Nat.cast_nonneg _)).mp hlogYpos |>.trans' zero_lt_one
  calc
    (n : ℝ) ^ (1 / 5 : ℝ) =
        Real.exp ((1 / 5 : ℝ) * L n) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      unfold L
      ring
    _ ≤ Real.exp (Real.log (yNat n : ℝ)) :=
      Real.exp_le_exp.mpr hlog
    _ = (yNat n : ℝ) := Real.exp_log hYpos





end

end Erdos390.Full.PaperPrimePowerTailRate

end

/- Source module: Erdos390.Full.FiniteLogStieltjes -/
section


/-!
# Finite logarithmic Stieltjes transfer

The physical column in the marked smooth-number argument is obtained from
uniform prefix-count estimates by Abel summation.  This file isolates the
exact deterministic step.  In particular, the error is charged only once
against the total variation of `log`; it is not multiplied by the number of
integer endpoints or by an auxiliary partition size.
-/

open scoped BigOperators Interval

namespace Erdos390.Full.FiniteLogStieltjes

open Finset MeasureTheory Set

noncomputable section

variable {Omega : Type*} [Fintype Omega]



/-- Summing the centered fiber masses over a finite set is exactly the
centered expectation of its value-preimage. -/
theorem sum_centeredFiberMass_eq
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (A : Omega → ℝ) (s : Finset ℕ) :
    (∑ k ∈ s, centeredFiberMass mu value A k) =
      ∑ omega, if value omega ∈ s then
        mu.mass omega * (A omega - mu.expect A) else 0 := by
  unfold centeredFiberMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hv : value omega ∈ s
  · rw [if_pos hv]
    rw [Finset.sum_eq_single (value omega)]
    · simp
    · intro k hk hne
      simp [hne.symm]
    · exact fun h ↦ (h hv).elim
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : value omega ≠ k := by
      intro h
      apply hv
      simpa [h] using hk
    simp [hne]









end

end Erdos390.Full.FiniteLogStieltjes

end

/- Source module: Erdos390.Full.PaperMediumNuisanceInputReduction -/
section


/-!
# Exact reductions for the two medium-law nuisance inputs

The nuisance Schur row in paper Lemma 8.6 uses two arithmetic facts about
the literal medium-prime component laws:

* a Stieltjes bound for `Cov(v_p, log (m / n))` inside one cell; and
* agreement, to reciprocal-logarithmic precision, of `E v_p` in two cells.

This file proves all finite probability, Abel summation, prime-power
summation, and physical-log identifications surrounding those two facts.
It intentionally does **not** replace the remaining arithmetic estimates by
a bundled certificate.  The hypotheses in the two terminal reductions are
the literal moving-prefix estimate and the literal prime-power/tail
estimates which still have to be obtained from the marked-cell theorem.
-/

open scoped BigOperators Interval

namespace Erdos390.Full

noncomputable section

open ArithmeticModel FiniteProbability ValuationScoreDomination
open DivisibilityMomentBounds

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- Subtracting a deterministic constant from the right statistic does not
change covariance.  This is used to pass exactly from `log m` to
`log (m / n)`. -/
theorem covariance_sub_const_right
    (mu : FiniteProbability Omega) (F G : Omega → ℝ) (a : ℝ) :
    mu.covariance F (fun omega ↦ G omega - a) = mu.covariance F G := by
  unfold covariance expect
  rw [show (∑ omega, mu.mass omega * (G omega - a)) =
      (∑ omega, mu.mass omega * G omega) -
        a * (∑ omega, mu.mass omega) by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro omega _
    ring]
  rw [show (∑ omega, mu.mass omega * (F omega * (G omega - a))) =
      (∑ omega, mu.mass omega * (F omega * G omega)) -
        a * (∑ omega, mu.mass omega * F omega) by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro omega _
    ring]
  rw [mu.mass_sum]
  ring























































end FiniteProbability

namespace PrimePowerTaylorLedger

open LocalFugacityBounds PrimePowerLcmGeometry















end PrimePowerTaylorLedger

namespace FiniteProbability

open PrimePowerTaylorLedger

variable {Omega : Type*} [Fintype Omega]



















end FiniteProbability

namespace FiniteLogStieltjes

open Finset Set

variable {Omega : Type*} [Fintype Omega]



/-- A centered cumulative fiber mass is exactly covariance with the
corresponding prefix indicator.  This identity lets the existing literal
guard-deletion covariance estimate act directly on moving prefixes. -/
theorem sum_centeredFiberMass_Icc_eq_covariance_prefixIndicator
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (A : Omega → ℝ) (k : ℕ) :
    (∑ j ∈ Icc 0 k, centeredFiberMass mu value A j) =
      mu.covariance A (fun omega ↦ if value omega ≤ k then 1 else 0) := by
  rw [sum_centeredFiberMass_eq]
  unfold FiniteProbability.covariance FiniteProbability.expect
  simp only [Finset.mem_Icc, Nat.zero_le, true_and]
  let EA : ℝ := ∑ eta, mu.mass eta * A eta
  let prefixMass : ℝ :=
    ∑ omega, if value omega ≤ k then mu.mass omega else 0
  let markedMass : ℝ :=
    ∑ omega, if value omega ≤ k then
      mu.mass omega * A omega else 0
  have hleft :
      (∑ omega, if value omega ≤ k then
          mu.mass omega * (A omega - EA) else 0) =
        markedMass - EA * prefixMass := by
    dsimp only [markedMass, prefixMass]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro omega homega
    by_cases h : value omega ≤ k
    · simp [h]
      ring
    · simp [h]
  have hmarked :
      (∑ omega, mu.mass omega *
        (A omega * if value omega ≤ k then 1 else 0)) =
          markedMass := by
    dsimp only [markedMass]
    apply Finset.sum_congr rfl
    intro omega homega
    by_cases h : value omega ≤ k <;> simp [h]
  have hprefix :
      (∑ omega, mu.mass omega *
        (if value omega ≤ k then 1 else 0)) = prefixMass := by
    dsimp only [prefixMass]
    apply Finset.sum_congr rfl
    intro omega homega
    by_cases h : value omega ≤ k <;> simp [h]
  change
    (∑ omega, if value omega ≤ k then
      mu.mass omega * (A omega - EA) else 0) = _
  rw [hleft, hmarked, hprefix]

end FiniteLogStieltjes

namespace GuardedUniformCell

open FiniteLogStieltjes

variable {Alpha : Type*} [DecidableEq Alpha]

/-- Literal guard deletion preserves a uniform moving-prefix estimate with
the explicit covariance perturbation `12 * KA * deletedMass`.  Thus guard
bookkeeping does not require a separate analytic assumption. -/
theorem exists_deleteGuards_centeredPrefix_bound
    (S G : Finset Alpha) (hS : S.Nonempty)
    (score : S → ℝ) (Kscore : ℝ)
    (hscore : ∀ x, |score x| ≤ Kscore)
    (value : S → ℕ) (A : S → ℝ) {KA E : ℝ}
    (hKA : 0 ≤ KA) (hA : ∀ x, |A x| ≤ KA)
    (hsmallCensus :
      Real.exp (2 * Kscore) * (G.card : ℝ) / (S.card : ℝ) ≤
        (1 : ℝ) / 2)
    (hprefix : ∀ k,
      |∑ j ∈ Finset.Icc 0 k,
        centeredFiberMass
          ((uniformOnFinset S hS).exponentialTilt score) value A j| ≤ E) :
    ∃ hsmall :
        ((uniformOnFinset S hS).exponentialTilt score).guardMass
          (guardSubtype S G) < 1,
      ∀ k,
        |∑ j ∈ Finset.Icc 0 k,
          centeredFiberMass
            (((uniformOnFinset S hS).exponentialTilt score).deleteGuards
              (guardSubtype S G) hsmall) value A j| ≤
          E + 12 * KA *
            (Real.exp (2 * Kscore) * (G.card : ℝ) / (S.card : ℝ)) := by
  let mu := (uniformOnFinset S hS).exponentialTilt score
  let guards := guardSubtype S G
  let delta := Real.exp (2 * Kscore) * (G.card : ℝ) / (S.card : ℝ)
  have hmass : mu.guardMass guards ≤ delta := by
    simpa only [mu, guards, delta] using
      tilted_uniform_guardMass_le S G hS score Kscore hscore
  have hhalf : mu.guardMass guards ≤ (1 : ℝ) / 2 :=
    hmass.trans hsmallCensus
  have hsmall : mu.guardMass guards < 1 := by linarith
  refine ⟨hsmall, ?_⟩
  intro k
  let I : S → ℝ := fun x ↦ if value x ≤ k then 1 else 0
  have hI0 : 0 ≤ (1 : ℝ) := by norm_num
  have hI : ∀ x, |I x| ≤ (1 : ℝ) := by
    intro x
    dsimp only [I]
    split_ifs <;> norm_num
  have hperturb := mu.guardPerturbation_le_four_mul_guardMass guards hhalf
  have hdiffRaw := mu.abs_deleteGuards_covariance_sub_le
    guards hsmall A I hKA hI0 hA hI
  have hmass0 : 0 ≤ mu.guardMass guards := mu.guardMass_nonneg guards
  have hdelta0 : 0 ≤ delta := by
    dsimp only [delta]
    positivity
  have hdiff :
      |(mu.deleteGuards guards hsmall).covariance A I -
          mu.covariance A I| ≤ 12 * KA * delta := by
    calc
      |(mu.deleteGuards guards hsmall).covariance A I -
          mu.covariance A I| ≤
        3 * KA * 1 * mu.guardPerturbation guards := hdiffRaw
      _ ≤ 3 * KA * 1 * (4 * mu.guardMass guards) := by
        exact mul_le_mul_of_nonneg_left hperturb
          (mul_nonneg (mul_nonneg (by norm_num) hKA) (by norm_num))
      _ ≤ 3 * KA * 1 * (4 * delta) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hmass (by norm_num)
        · positivity
      _ = 12 * KA * delta := by ring
  have hbase : |mu.covariance A I| ≤ E := by
    rw [← sum_centeredFiberMass_Icc_eq_covariance_prefixIndicator]
    simpa only [mu, I] using hprefix k
  have hdeleted :
      |(mu.deleteGuards guards hsmall).covariance A I| ≤
        12 * KA * delta + E := by
    calc
      |(mu.deleteGuards guards hsmall).covariance A I| ≤
        |(mu.deleteGuards guards hsmall).covariance A I -
            mu.covariance A I| + |mu.covariance A I| := by
          have h := abs_add_le
            ((mu.deleteGuards guards hsmall).covariance A I -
              mu.covariance A I) (mu.covariance A I)
          simpa only [sub_add_cancel] using h
      _ ≤ 12 * KA * delta + E := add_le_add hdiff hbase
  rw [sum_centeredFiberMass_Icc_eq_covariance_prefixIndicator]
  simpa only [I, mu, guards, delta, add_comm] using hdeleted



end GuardedUniformCell

namespace PrimePowerTail

open Finset

variable {Omega : Type*} [Fintype Omega]



end PrimePowerTail

namespace PaperBridgeFit

open ArithmeticBandGeometry FiniteLogStieltjes

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)













end BridgeData

end PaperBridgeFit

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperRawTiltedPrefixRowUnrestricted -/
section


/-!
# Raw tilted moving-prefix row with an unrestricted fixed coefficient box

This is the parameter-order-safe form of the raw row.  `W` and the box
radius are arbitrary fixed parameters.  The score envelope
`2 B / log W` enters only through a fixed exponential constant; no relation
between the box radius and `W` is assumed.
-/

open Filter Topology

namespace Erdos390.Full.PaperRawTiltedPrefixRowUnrestricted

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimeSums ValuationScoreDomination ValuationTiltCell
open PaperScaleMarkedCell FullTiltPairChamber
open PaperRawPrefixValuationRow
open PaperRawTiltedPrefixRow

noncomputable section

set_option maxHeartbeats 1600000



/-- All-prefix unrestricted terminal. -/
theorem exists_uniform_rawCell_tilted_valuation_all_prefix_rate_unrestricted
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (B : ℝ) (W : ℕ)
    (hB : 0 ≤ B) (hW : 1 < W)
    (hHeadLe : ∀ q ∈ H.primes, q ≤ W) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ {n k p : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        (∀ q ∈ primeBand n W, |eta q| ≤ B) →
        let S := structuredCell H (physicalBound A n) (physicalBound C n)
          (yNat n)
        ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
                (fun m : S ↦
                  valuationScore (primeBand n W) eta (L n) (m : ℕ))).covariance
              (fun m : S ↦ valuation p (m : ℕ))
              (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
            epsilon n / (p : ℝ) := by
  obtain ⟨epsilon₀, hepsilon₀, N₀, hprefix⟩ :=
    exists_uniform_rawCell_tilted_valuation_prefix_rate_unrestricted
      H hA hAC hC B W hB hW hHeadLe
  let epsilon : ℕ → ℝ := fun n ↦ |epsilon₀ n|
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog0 : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (L n) :=
    (hLTop.eventually (eventually_ge_atTop 1)).mono fun n hn ↦
      Real.log_nonneg hn
  have hepsilon : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have habs' : Tendsto (fun n : ℕ ↦
        |epsilon₀ n * Real.log (L n)|) atTop (nhds 0) := by
      simpa only [abs_zero] using hepsilon₀.abs
    apply habs'.congr'
    filter_upwards [hlog0] with n hn
    dsimp only [epsilon]
    rw [abs_mul, abs_of_nonneg hn]
  refine ⟨epsilon, fun n ↦ abs_nonneg _, hepsilon, N₀, ?_⟩
  intro n k p eta hN hpBand heta
  let S := structuredCell H (physicalBound A n) (physicalBound C n)
    (yNat n)
  change ∀ hS : S.Nonempty, _
  intro hS
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hpBand).pos
  have hepsilonLe : epsilon₀ n / (p : ℝ) ≤ epsilon n / (p : ℝ) :=
    div_le_div_of_nonneg_right (le_abs_self (epsilon₀ n)) hpR.le
  by_cases hlow : physicalBound A n < k
  · by_cases hhigh : k ≤ physicalBound C n
    · exact (hprefix eta hN hlow hhigh hpBand heta hS).trans hepsilonLe
    · have hconst :
          (fun m : S ↦ if (m : ℕ) ≤ k then (1 : ℝ) else 0) =
            fun _ ↦ 1 := by
        funext m
        have hmC : (m : ℕ) ≤ physicalBound C n :=
          (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
        rw [if_pos (hmC.trans (Nat.le_of_not_ge hhigh))]
      rw [hconst]
      have hcov : ((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore (primeBand n W) eta (L n)
            (m : ℕ))).covariance
          (fun m : S ↦ valuation p (m : ℕ)) (fun _ ↦ 1) = 0 := by
        let nu := (uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore (primeBand n W) eta (L n)
            (m : ℕ))
        calc
          nu.covariance (fun m : S ↦ valuation p (m : ℕ))
              (fun _ ↦ 1) =
            nu.covariance (fun m : S ↦ valuation p (m : ℕ))
              (fun _ ↦ 0) := by
                simpa using (nu.covariance_sub_const_right
                  (fun m : S ↦ valuation p (m : ℕ)) (fun _ ↦ 0) (-1))
          _ = 0 := nu.covariance_zero_right _
      rw [hcov, abs_zero]
      exact div_nonneg (abs_nonneg _) hpR.le
  · have hconst :
        (fun m : S ↦ if (m : ℕ) ≤ k then (1 : ℝ) else 0) =
          fun _ ↦ 0 := by
      funext m
      have hAm : physicalBound A n < (m : ℕ) :=
        (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).1
      rw [if_neg (not_le_of_gt ((Nat.le_of_not_gt hlow).trans_lt hAm))]
    rw [hconst,
      ((uniformOnFinset S hS).exponentialTilt
        (fun m : S ↦ valuationScore (primeBand n W) eta (L n)
          (m : ℕ))).covariance_zero_right,
      abs_zero]
    exact div_nonneg (abs_nonneg _) hpR.le

end

end Erdos390.Full.PaperRawTiltedPrefixRowUnrestricted

end

/- Source module: Erdos390.Full.PaperFixedFiniteRawTiltedPrefixRows -/
section


/-!
# A common raw tilted prefix rate for a fixed finite family of cells

The canonical bridge has finitely many head/physical cells.  This file takes
the finite sum of the independently proved cell rates, producing one
nonnegative rate and one threshold that work simultaneously in every cell.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperFixedFiniteRawTiltedPrefixRows

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability ValuationScoreDomination
open PaperRawTiltedPrefixRow
open PaperRawTiltedPrefixRowUnrestricted

noncomputable section

variable {Cell : Type*} [Fintype Cell]



/-- Fixed-finite aggregation of the parameter-order-safe unrestricted raw
row. -/
theorem exists_uniform_fixedFinite_rawCell_tilted_valuation_all_prefix_rate_unrestricted
    (H : Cell → Pattern) (A C : Cell → ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c)
    (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W)
    (hHeadLe : ∀ c, ∀ q ∈ (H c).primes, q ≤ W) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ (c : Cell) {n k p : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        (∀ q ∈ primeBand n W, |eta q| ≤ B) →
        let S := structuredCell (H c) (physicalBound (A c) n)
          (physicalBound (C c) n) (yNat n)
        ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
                (fun m : S ↦
                  valuationScore (primeBand n W) eta (L n) (m : ℕ))).covariance
              (fun m : S ↦ valuation p (m : ℕ))
              (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
            epsilon n / (p : ℝ) := by
  have hexists : ∀ c : Cell, ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ {n k p : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        (∀ q ∈ primeBand n W, |eta q| ≤ B) →
        let S := structuredCell (H c) (physicalBound (A c) n)
          (physicalBound (C c) n) (yNat n)
        ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
                (fun m : S ↦
                  valuationScore (primeBand n W) eta (L n) (m : ℕ))).covariance
              (fun m : S ↦ valuation p (m : ℕ))
              (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
            epsilon n / (p : ℝ) := by
    intro c
    exact exists_uniform_rawCell_tilted_valuation_all_prefix_rate_unrestricted
      (H c) (hA c) (hAC c) (hC c) B W hB hW (hHeadLe c)
  choose epsilonCell hepsilonCell0 hepsilonCellRate Ncell hcell using hexists
  let epsilon : ℕ → ℝ := fun n ↦ ∑ c : Cell, epsilonCell c n
  let N₀ : ℕ := ∑ c : Cell, Ncell c
  have hepsilon0 : ∀ n, 0 ≤ epsilon n := by
    intro n
    dsimp only [epsilon]
    exact Finset.sum_nonneg fun c hc ↦ hepsilonCell0 c n
  have hepsilonRate : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have hsum := tendsto_finset_sum (Finset.univ : Finset Cell)
      (fun c hc ↦ hepsilonCellRate c)
    have hsum' : Tendsto (fun n : ℕ ↦
        ∑ c : Cell, epsilonCell c n * Real.log (L n))
        atTop (nhds 0) := by
      simpa only [Finset.sum_const_zero] using hsum
    apply hsum'.congr'
    filter_upwards with n
    dsimp only [epsilon]
    rw [Finset.sum_mul]
  refine ⟨epsilon, hepsilon0, hepsilonRate, N₀, ?_⟩
  intro c n k p eta hN hpBand heta
  have hNc : Ncell c ≤ N₀ := by
    dsimp only [N₀]
    exact Finset.single_le_sum
      (fun d hd ↦ Nat.zero_le (Ncell d)) (Finset.mem_univ c)
  let S := structuredCell (H c) (physicalBound (A c) n)
    (physicalBound (C c) n) (yNat n)
  change ∀ hS : S.Nonempty, _
  intro hS
  have hraw := hcell c (n := n) (k := k) (p := p)
    eta (hNc.trans hN) hpBand heta hS
  have hcellLe : epsilonCell c n ≤ epsilon n := by
    dsimp only [epsilon]
    exact Finset.single_le_sum
      (fun d hd ↦ hepsilonCell0 d n) (Finset.mem_univ c)
  have hpR : (0 : ℝ) ≤ p := by positivity
  simpa only [S] using
    hraw.trans (div_le_div_of_nonneg_right hcellLe hpR)

end

end Erdos390.Full.PaperFixedFiniteRawTiltedPrefixRows

end

/- Source module: Erdos390.Full.PaperCanonicalMediumNuisanceRows -/
section


/-!
# Canonical raw-cell attachment for the medium nuisance rows

This file contains the dependent-type bookkeeping which identifies the
guard-deleted exponential tilt on a literal raw structured cell with the
`cellMediumLaw` carried by canonical `BridgeData`.  In particular, later
moving-prefix and prime-power estimates can be proved on the raw cell and
transported to the exact laws used by the nuisance Schur complement without
an unrecorded change of sample space.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus GuardedUniformCell ValuationScoreDomination

namespace FiniteProbability

variable {Alpha : Type*}



/-- Covariance analogue of
`uniformOnFinset_exponentialTilt_expect_eq_of_finset_eq`. -/
theorem uniformOnFinset_exponentialTilt_covariance_eq_of_finset_eq
    (S T : Finset Alpha) (hST : S = T)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (scoreS : S → ℝ) (scoreT : T → ℝ)
    (hscore : ∀ (x : S) (y : T), (x : Alpha) = (y : Alpha) →
      scoreS x = scoreT y)
    (F H : Alpha → ℝ) :
    ((uniformOnFinset S hS).exponentialTilt scoreS).covariance
        (fun x ↦ F (x : Alpha)) (fun x ↦ H (x : Alpha)) =
      ((uniformOnFinset T hT).exponentialTilt scoreT).covariance
        (fun x ↦ F (x : Alpha)) (fun x ↦ H (x : Alpha)) := by
  subst T
  have hscoreEq : scoreS = scoreT := by
    funext x
    exact hscore x x rfl
  subst scoreT
  have hproof : hS = hT := Subsingleton.elim _ _
  subst hT
  rfl

end FiniteProbability

namespace PaperBridgeFit

open HeadPattern

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Exact covariance reindexing from the raw tilted cell after deleting the
concrete guards to the canonical `cellMediumLaw`. -/
theorem raw_deleteGuards_covariance_eq_cellMediumLaw
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : Ledger B.sampleData.n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hremaining : ∀ c : Cell Head,
      (rawCell P I B.sampleData.n c \ G.guards).Nonempty)
    (hcanonical : B.sampleData =
      canonicalSampleData (W := B.sampleData.W) P I G hsep hremaining)
    (xi : B.ParamSpace) (c : Cell Head)
    (hsmall :
      ((uniformOnFinset (rawCell P I B.sampleData.n c)
        ((hremaining c).mono Finset.sdiff_subset)).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).guardMass
        (guardSubtype (rawCell P I B.sampleData.n c) G.guards) < 1)
    (F H : ℕ → ℝ) :
    (((uniformOnFinset (rawCell P I B.sampleData.n c)
        ((hremaining c).mono Finset.sdiff_subset)).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).deleteGuards
        (guardSubtype (rawCell P I B.sampleData.n c) G.guards) hsmall).covariance
          (fun m ↦ F (m : ℕ)) (fun m ↦ H (m : ℕ)) =
      (B.cellMediumLaw xi c).covariance
        (fun m ↦ F (m : ℕ)) (fun m ↦ H (m : ℕ)) := by
  let S := rawCell P I B.sampleData.n c
  let hS : S.Nonempty := (hremaining c).mono Finset.sdiff_subset
  let score : S → ℝ := fun m ↦ valuationScore
    (primeBand B.sampleData.n B.sampleData.W)
    (B.effectiveNatCoefficient xi) B.L (m : ℕ)
  have hreindex := deleteGuards_tilted_uniform_covariance_remaining_eq
    S G.guards hS (hremaining c) score hsmall
      (fun m ↦ F (m : ℕ)) (fun m ↦ H (m : ℕ))
  have hcellEq : B.sampleData.cellFinset c = S \ G.guards := by
    calc
      B.sampleData.cellFinset c =
          (canonicalSampleData (W := B.sampleData.W)
            P I G hsep hremaining).cellFinset c :=
        congrArg (fun D : StructuredSampleData Head ↦ D.cellFinset c)
          hcanonical
      _ = S \ G.guards := by
        simpa only [S] using
          canonicalSampleData_cellFinset P I G hsep hremaining c
  have htilt :=
    uniformOnFinset_exponentialTilt_covariance_eq_of_finset_eq
      (S \ G.guards) (B.sampleData.cellFinset c) hcellEq.symm
      (hremaining c) (B.sampleData.cell_nonempty c)
      (fun z ↦ score (remainingEmbedding S G.guards z))
      (sigmaCellScore (B.scaledMediumScore xi) c)
      (by
        intro x y hxy
        rw [B.sigmaCellScore_scaledMedium_eq_valuationScore xi c y]
        dsimp only [score]
        rw [remainingEmbedding_value, hxy]) F H
  exact hreindex.trans htilt

/-- A raw tilted moving-prefix bound survives the canonical guard deletion
with the literal census error.  The conclusion is stated directly for
`cellMediumLaw`, so no subtype identification is left to downstream uses. -/
theorem cellMediumLaw_prefix_bound_of_raw_tilt
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : Ledger B.sampleData.n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hremaining : ∀ c : Cell Head,
      (rawCell P I B.sampleData.n c \ G.guards).Nonempty)
    (hcanonical : B.sampleData =
      canonicalSampleData (W := B.sampleData.W) P I G hsep hremaining)
    (xi : B.ParamSpace) (c : Cell Head) (p : ℕ)
    {Kscore KA E : ℝ}
    (hKA : 0 ≤ KA)
    (hscore : ∀ m : rawCell P I B.sampleData.n c,
      |valuationScore (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ Kscore)
    (hvaluation : ∀ m : rawCell P I B.sampleData.n c,
      |(valuation p (m : ℕ) : ℝ)| ≤ KA)
    (hsmallCensus :
      Real.exp (2 * Kscore) * (G.guards.card : ℝ) /
        ((rawCell P I B.sampleData.n c).card : ℝ) ≤ (1 : ℝ) / 2)
    (hprefix : ∀ k : ℕ,
      |((uniformOnFinset (rawCell P I B.sampleData.n c)
          ((hremaining c).mono Finset.sdiff_subset)).exponentialTilt
        (fun m ↦ valuationScore
          (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ))).covariance
          (fun m ↦ (valuation p (m : ℕ) : ℝ))
          (fun m ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤ E) :
    ∀ k : ℕ,
      |(B.cellMediumLaw xi c).covariance
          (fun m ↦ (valuation p (m : ℕ) : ℝ))
          (fun m ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
        E + 12 * KA *
          (Real.exp (2 * Kscore) * (G.guards.card : ℝ) /
            ((rawCell P I B.sampleData.n c).card : ℝ)) := by
  let S := rawCell P I B.sampleData.n c
  let hS : S.Nonempty := (hremaining c).mono Finset.sdiff_subset
  let score : S → ℝ := fun m ↦ valuationScore
    (primeBand B.sampleData.n B.sampleData.W)
    (B.effectiveNatCoefficient xi) B.L (m : ℕ)
  let value : S → ℕ := fun m ↦ (m : ℕ)
  let V : S → ℝ := fun m ↦ (valuation p (m : ℕ) : ℝ)
  have hprefixCentered : ∀ k,
      |∑ j ∈ Finset.Icc 0 k,
        FiniteLogStieltjes.centeredFiberMass
          ((uniformOnFinset S hS).exponentialTilt score) value V j| ≤ E := by
    intro k
    rw [FiniteLogStieltjes.sum_centeredFiberMass_Icc_eq_covariance_prefixIndicator]
    simpa only [S, hS, score, value, V] using hprefix k
  obtain ⟨hsmall, hdeleted⟩ :=
    GuardedUniformCell.exists_deleteGuards_centeredPrefix_bound
      S G.guards hS score Kscore
      (by simpa only [S, score] using hscore)
      value V hKA (by simpa only [S, V] using hvaluation)
      (by simpa only [S] using hsmallCensus) hprefixCentered
  intro k
  have hdelCov := hdeleted k
  rw [FiniteLogStieltjes.sum_centeredFiberMass_Icc_eq_covariance_prefixIndicator]
    at hdelCov
  have hreindex := B.raw_deleteGuards_covariance_eq_cellMediumLaw
    P I G hsep hremaining hcanonical xi c hsmall
      (fun m ↦ (valuation p m : ℝ))
      (fun m ↦ if m ≤ k then 1 else 0)
  rw [hreindex] at hdelCov
  simpa only [S, hS, score, value, V] using hdelCov





end BridgeData

end PaperBridgeFit

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperCanonicalTiltedPrefixRows -/
section


/-!
# Canonical guard-deleted tilted moving-prefix rows

The raw Taylor row is transported through the literal guard deletion and
the exact canonical sample-space reindexing.  After row normalization, the
guard error contains the factor `p * valuationEnvelope`.  Uniformly in the
moving band this is eventually at most `yNat^2`, so it is absorbed by the
already audited squarefree guard error.  The final coefficient therefore
still satisfies the sharp `epsilon(n) * log L(n) -> 0` rate.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperCanonicalTiltedPrefixRows

open ArithmeticModel Scale HeadPattern StructuredCells
open ArithmeticBandGeometry _root_.Erdos390.Full.PaperBridgeFit
open FiniteProbability ValuationScoreDomination ValuationTiltCell
open PaperGuardCensus GuardDeletionSquarefreeProfiles
open GuardSquarefreeErrorRate PaperPrimePowerTailRate
open PaperFixedFiniteRawTiltedPrefixRows

noncomputable section

set_option maxHeartbeats 1600000

/-- Every fixed multiple of `L` is eventually below `yNat`.  The proof uses
the explicit intermediate scale `n^(1/5)`, safely below `y=n^(2/9)`. -/
theorem eventually_two_div_log_mul_L_le_yNat
    (W : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (2 / Real.log (W : ℝ)) * L n ≤ (yNat n : ℝ) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (1 : ℝ) / x ^ (1 / 5 : ℝ))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 5)).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto
      (fun n : ℕ ↦ L n / (n : ℝ) ^ (1 / 5 : ℝ))
      atTop (nhds 0) := by
    change Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) /
        (n : ℝ) ^ (1 / 5 : ℝ)) atTop (nhds 0)
    simpa only [Function.comp_apply, Real.rpow_one] using hnat
  let K : ℝ := 2 / Real.log (W : ℝ)
  have hscaled : Tendsto
      (fun n : ℕ ↦ (K * L n) / (n : ℝ) ^ (1 / 5 : ℝ))
      atTop (nhds 0) := by
    have hK : Tendsto (fun _n : ℕ ↦ K) atTop (nhds K) :=
      tendsto_const_nhds
    have hraw := hK.mul hbase
    have hraw' : Tendsto
        (fun n : ℕ ↦ K * (L n / (n : ℝ) ^ (1 / 5 : ℝ)))
        atTop (nhds 0) := by simpa only [mul_zero] using hraw
    apply hraw'.congr'
    filter_upwards with n
    ring
  have hle : ∀ᶠ n : ℕ in atTop,
      (K * L n) / (n : ℝ) ^ (1 / 5 : ℝ) ≤ 1 :=
    hscaled.eventually (eventually_le_nhds (by norm_num))
  filter_upwards [hle, eventually_rpow_one_fifth_le_yNat,
    Filter.eventually_gt_atTop 0] with n hratio hpow hn
  have hden : 0 < (n : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hKL : K * L n ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
    have := (div_le_iff₀ hden).mp hratio
    simpa only [one_mul] using this
  simpa only [K] using hKL.trans hpow

/-- Uniform logarithmic envelope bounds for the fixed finite family of
physical cells.  Both nonnegativity and the precise fixed-cutoff multiple of
`L` are retained for downstream multiplication. -/
theorem eventually_valuationEnvelope_bounds
    {Head : Type*} [Fintype Head]
    (I : PhysicalIntervals) (W : ℕ) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ c : PaperBridgeFit.Cell Head,
      0 ≤ valuationEnvelope I n W c ∧
      valuationEnvelope I n W c ≤
        (2 / Real.log (W : ℝ)) * L n := by
  rw [Filter.eventually_all]
  intro c
  let C : ℝ := I.upper c.2
  have hC : 0 < C := (I.lower_pos c.2).trans (I.lower_lt_upper c.2)
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hCevent : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop C)
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  filter_upwards [hCevent, hInvCevent, Filter.eventually_gt_atTop 1]
      with n hCn hInvCn hn
  have hnR : (0 : ℝ) < n := by positivity
  have hL : 0 < L n := L_pos hn
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  let M := physicalBound C n
  have hMcast : (M : ℝ) ≤ C * (n : ℝ) := by
    dsimp only [M]
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le hnR.le)
  have hMone : 1 ≤ M := by
    dsimp only [M]
    unfold physicalBound
    apply Nat.le_floor
    have hraw := (div_le_iff₀ hC).mp hInvCn
    exact_mod_cast (show (1 : ℝ) ≤ C * (n : ℝ) by
      simpa only [one_mul, mul_comm] using hraw)
  have hMpos : 0 < M := Nat.zero_lt_of_lt hMone
  have hCnSq : C * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hlogM : Real.log (M : ℝ) ≤ 2 * L n := by
    have hle : (M : ℝ) ≤ (n : ℝ) ^ 2 := hMcast.trans hCnSq
    have hraw := Real.log_le_log (by exact_mod_cast hMpos) hle
    rw [Real.log_pow] at hraw
    simpa [L] using hraw
  have henv0 : 0 ≤ valuationEnvelope I n W c := by
    unfold valuationEnvelope
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hMone)) hlogW.le
  refine ⟨henv0, ?_⟩
  unfold valuationEnvelope
  change Real.log (M : ℝ) / Real.log (W : ℝ) ≤ _
  calc
    Real.log (M : ℝ) / Real.log (W : ℝ) ≤
        (2 * L n) / Real.log (W : ℝ) :=
      div_le_div_of_nonneg_right hlogM hlogW.le
    _ = (2 / Real.log (W : ℝ)) * L n := by ring

/-- Row-normalized guard envelope: `p * valuationEnvelope <= yNat^2`
uniformly in the cell and moving band prime. -/
theorem eventually_bandPrime_mul_valuationEnvelope_le_yNat_sq
    {Head : Type*} [Fintype Head]
    (I : PhysicalIntervals) (W : ℕ) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (c : PaperBridgeFit.Cell Head) (p : BandPrime n W),
        (p.1 : ℝ) * valuationEnvelope I n W c ≤ (yNat n : ℝ) ^ 2 := by
  filter_upwards [eventually_valuationEnvelope_bounds (Head := Head) I W hW,
    eventually_two_div_log_mul_L_le_yNat W] with n henv hscale
  intro c p
  have hpY : (p.1 : ℝ) ≤ (yNat n : ℝ) := by
    exact_mod_cast le_yNat_of_mem_primeBand p.2
  have henvY : valuationEnvelope I n W c ≤ (yNat n : ℝ) :=
    (henv c).2.trans hscale
  have hy0 : (0 : ℝ) ≤ yNat n := by positivity
  have hmul := mul_le_mul hpY henvY (henv c).1 hy0
  simpa only [pow_two] using hmul







namespace PaperBridgeFit.BridgeData

open _root_.Erdos390.Full.PaperBridgeFit

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

/-- Canonical, guard-deleted terminal moving-prefix row.  No raw prefix,
third-cumulant, density, score-smallness, or guard estimate remains as a
hypothesis.  The threshold is uniform in the bridge data, the effective
coefficient vector, all cells, all prefixes, and all moving primes. -/
theorem exists_uniform_canonical_cellMediumLaw_tilted_valuation_prefix_rate_unrestricted
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (P h).primes, q ≤ W)
    (Acoef : ℝ) (hAcoef : 0 ≤ Acoef) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ,
        ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
          (B : BridgeData Head Band) (xi : B.ParamSpace),
          N₀ ≤ B.sampleData.n → B.sampleData.W = W →
          (∀ p : BandPrime B.sampleData.n B.sampleData.W,
            |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n) →
          (hremaining : ∀ c : Cell Head,
            (rawCell P I B.sampleData.n c \ (G B.sampleData.n).guards).Nonempty) →
          B.sampleData = canonicalSampleData
            (W := B.sampleData.W) P I (G B.sampleData.n) hsep hremaining →
          ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
            (c : Cell Head) (k : ℕ),
            |(B.cellMediumLaw xi c).covariance
                (fun m ↦ (valuation p.1 (m : ℕ) : ℝ))
                (fun m ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
              epsilon B.sampleData.n / (p.1 : ℝ) := by
  let H : Cell Head → Pattern := fun c ↦ P c.1
  let Alower : Cell Head → ℝ := fun c ↦ I.lower c.2
  let Cupper : Cell Head → ℝ := fun c ↦ I.upper c.2
  obtain ⟨epsilonRaw, hepsilonRaw0, hepsilonRawRate, Nraw, hraw⟩ :=
    exists_uniform_fixedFinite_rawCell_tilted_valuation_all_prefix_rate_unrestricted
      H Alower Cupper
      (fun c ↦ I.lower_pos c.2)
      (fun c ↦ I.lower_lt_upper c.2)
      (fun c ↦ (I.lower_pos c.2).trans (I.lower_lt_upper c.2))
      Acoef W hAcoef hW (fun c ↦ hHeadLe c.1)
  let Kscore : ℝ := (2 * Acoef) / Real.log (W : ℝ)
  let epsilonGuard : ℕ → ℝ := fun n ↦
    6 * canonicalGuardSquarefreeError P I G Kscore n
  let epsilon : ℕ → ℝ := fun n ↦
    epsilonRaw n + epsilonGuard n
  have hepsilonGuard0 : ∀ n, 0 ≤ epsilonGuard n := by
    intro n
    dsimp only [epsilonGuard]
    exact mul_nonneg (by norm_num)
      (canonicalGuardSquarefreeError_nonneg P I G Kscore n)
  have hepsilon0 : ∀ n, 0 ≤ epsilon n := by
    intro n
    dsimp only [epsilon]
    exact add_nonneg (hepsilonRaw0 n) (hepsilonGuard0 n)
  have hepsilonGuardRate : Tendsto (fun n : ℕ ↦
      epsilonGuard n * Real.log (L n)) atTop (nhds 0) := by
    have hrawRate :=
      tendsto_canonicalGuardSquarefreeError_mul_logL_zero P I G Kscore
    have hsix : Tendsto (fun _n : ℕ ↦ (6 : ℝ)) atTop (nhds 6) :=
      tendsto_const_nhds
    have hmul := hsix.mul hrawRate
    simpa only [epsilonGuard, mul_zero, mul_assoc] using hmul
  have hepsilonRate : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have hsum := hepsilonRawRate.add hepsilonGuardRate
    simpa only [epsilon, add_mul, zero_add] using hsum
  have hsmallEvent :=
    eventually_exp_two_mul_guardRatio_rawCell_le_half
      P I Cprom Cbank G Kscore
  have henvEvent :=
    eventually_valuationEnvelope_bounds (Head := Head) I W hW
  have hrowEnvEvent :=
    eventually_bandPrime_mul_valuationEnvelope_le_yNat_sq
      (Head := Head) I W hW
  have hAll : ∀ᶠ n : ℕ in atTop,
      (∀ c : Cell Head,
        Real.exp (2 * Kscore) * ((G n).guards.card : ℝ) /
          ((rawCell P I n c).card : ℝ) ≤ (1 : ℝ) / 2) ∧
      (∀ c : Cell Head, 0 ≤ valuationEnvelope I n W c ∧
        valuationEnvelope I n W c ≤
          (2 / Real.log (W : ℝ)) * L n) ∧
      (∀ (c : Cell Head) (p : BandPrime n W),
        (p.1 : ℝ) * valuationEnvelope I n W c ≤
          (yNat n : ℝ) ^ 2) ∧ 1 < n := by
    filter_upwards [hsmallEvent, henvEvent, hrowEnvEvent,
      Filter.eventually_gt_atTop 1] with n hsmallN henvN hrowEnvN hn
    exact ⟨hsmallN, henvN, hrowEnvN, hn⟩
  obtain ⟨Nevent, hNevent⟩ := Filter.eventually_atTop.mp hAll
  refine ⟨epsilon, hepsilon0, hepsilonRate, max Nraw Nevent, ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW heta hsep hremaining hcanonical
  subst W
  have hNraw : Nraw ≤ B.sampleData.n := by omega
  have hNeventBound : Nevent ≤ B.sampleData.n := by omega
  obtain ⟨hsmallN, henvN, hrowEnvN, hn⟩ :=
    hNevent B.sampleData.n hNeventBound
  have hetaNat : ∀ q ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.effectiveNatCoefficient xi q| ≤ Acoef := by
    intro q hq
    rw [B.effectiveNatCoefficient_of_mem xi hq]
    exact heta ⟨q, hq⟩
  intro p c k
  have hpW : 1 < B.sampleData.W := hW
  have hrawPrefix : ∀ j : ℕ,
      |((uniformOnFinset (rawCell P I B.sampleData.n c)
          ((hremaining c).mono Finset.sdiff_subset)).exponentialTilt
        (fun m ↦ valuationScore
          (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ))).covariance
          (fun m ↦ (valuation p.1 (m : ℕ) : ℝ))
          (fun m ↦ if (m : ℕ) ≤ j then 1 else 0)| ≤
        epsilonRaw B.sampleData.n / (p.1 : ℝ) := by
    intro j
    have hrawJ := hraw c (n := B.sampleData.n) (k := j) (p := p.1)
      (B.effectiveNatCoefficient xi)
      hNraw p.2 hetaNat ((hremaining c).mono Finset.sdiff_subset)
    simpa only [H, Alower, Cupper, rawCell, BridgeData.L, Scale.L] using hrawJ
  have hL : 0 < B.L := B.L_pos
  have hlogW : 0 < Real.log (B.sampleData.W : ℝ) :=
    Real.log_pos (by exact_mod_cast hpW)
  have hscore : ∀ m : rawCell P I B.sampleData.n c,
      |valuationScore (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ Kscore := by
    intro m
    have hmpos : 0 < (m : ℕ) :=
      pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
    have hmM : (m : ℕ) ≤
        physicalBound (I.upper c.2) B.sampleData.n :=
      (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
    have hprimeW : ∀ q ∈ primeBand B.sampleData.n B.sampleData.W,
        B.sampleData.W ≤ q := by
      intro q hq
      exact (cutoff_lt_of_mem_primeBand hq).le
    have hscoreRaw := abs_valuationScore_le_log_ratio
      (primeBand B.sampleData.n B.sampleData.W)
      (B.effectiveNatCoefficient xi) hmpos hmM hpW hprimeW
      hAcoef hL hetaNat
    have henvUpper : valuationEnvelope I B.sampleData.n
        B.sampleData.W c ≤
          (2 / Real.log (B.sampleData.W : ℝ)) * B.L := by
      simpa only [BridgeData.L, Scale.L] using (henvN c).2
    have hcoef : 0 ≤ Acoef / B.L := div_nonneg hAcoef hL.le
    calc
      |valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤
        (Acoef / B.L) * valuationEnvelope I B.sampleData.n
          B.sampleData.W c := by
        simpa only [valuationEnvelope] using hscoreRaw
      _ ≤ (Acoef / B.L) *
          ((2 / Real.log (B.sampleData.W : ℝ)) * B.L) :=
        mul_le_mul_of_nonneg_left henvUpper hcoef
      _ = Kscore := by
        dsimp only [Kscore]
        field_simp [hL.ne', hlogW.ne']
  let KA := valuationEnvelope I B.sampleData.n B.sampleData.W c
  have hKA : 0 ≤ KA := by
    dsimp only [KA]
    exact (henvN c).1
  have hvaluation : ∀ m : rawCell P I B.sampleData.n c,
      |(valuation p.1 (m : ℕ) : ℝ)| ≤ KA := by
    intro m
    rw [abs_of_nonneg (valuation_nonneg p.1 (m : ℕ))]
    exact (rawCell_valuation_le_total P I p c m).trans
      (by simpa only [KA] using rawCell_totalBandValuation_le P I hpW c m)
  have hcanonicalPrefix := B.cellMediumLaw_prefix_bound_of_raw_tilt
    P I (G B.sampleData.n) hsep hremaining hcanonical xi c p.1 hKA
    hscore hvaluation (hsmallN c) hrawPrefix k
  let delta : ℝ := Real.exp (2 * Kscore) *
    ((G B.sampleData.n).guards.card : ℝ) /
      ((rawCell P I B.sampleData.n c).card : ℝ)
  have hdelta0 : 0 ≤ delta := by
    dsimp only [delta]
    have hguardCard : (0 : ℝ) ≤ ((G B.sampleData.n).guards.card : ℝ) := by
      exact_mod_cast Nat.zero_le (G B.sampleData.n).guards.card
    have hrawCard : (0 : ℝ) ≤
        ((rawCell P I B.sampleData.n c).card : ℝ) := by
      exact_mod_cast Nat.zero_le (rawCell P I B.sampleData.n c).card
    exact div_nonneg
      (mul_nonneg (Real.exp_pos _).le hguardCard) hrawCard
  have hpR : (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have hrowEnv : (p.1 : ℝ) * KA ≤
      (yNat B.sampleData.n : ℝ) ^ 2 := by
    simpa only [KA] using hrowEnvN c p
  have hguardCell :
      (p.1 : ℝ) * (12 * KA * delta) ≤
        6 * guardSquarefreeError
          (rawCell P I B.sampleData.n c) (G B.sampleData.n).guards
            Kscore B.sampleData.n := by
    unfold guardSquarefreeError
    dsimp only [delta]
    calc
      (p.1 : ℝ) *
          (12 * KA *
            (Real.exp (2 * Kscore) *
              ((G B.sampleData.n).guards.card : ℝ) /
                ((rawCell P I B.sampleData.n c).card : ℝ))) =
        12 * ((p.1 : ℝ) * KA) *
          (Real.exp (2 * Kscore) *
            ((G B.sampleData.n).guards.card : ℝ) /
              ((rawCell P I B.sampleData.n c).card : ℝ)) := by ring
      _ ≤ 12 * (yNat B.sampleData.n : ℝ) ^ 2 *
          (Real.exp (2 * Kscore) *
            ((G B.sampleData.n).guards.card : ℝ) /
              ((rawCell P I B.sampleData.n c).card : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrowEnv (by norm_num)) hdelta0
      _ = 6 *
          (2 * (Real.exp (2 * Kscore) *
            ((G B.sampleData.n).guards.card : ℝ) /
              ((rawCell P I B.sampleData.n c).card : ℝ)) *
                (yNat B.sampleData.n : ℝ) ^ 2) := by ring
  have hcellToSum : guardSquarefreeError
      (rawCell P I B.sampleData.n c) (G B.sampleData.n).guards
        Kscore B.sampleData.n ≤
      canonicalGuardSquarefreeError P I G Kscore B.sampleData.n := by
    unfold canonicalGuardSquarefreeError
    exact Finset.single_le_sum
      (fun d hd ↦ guardSquarefreeError_nonneg
        (rawCell P I B.sampleData.n d) (G B.sampleData.n).guards
          Kscore B.sampleData.n)
      (Finset.mem_univ c)
  have hguardRow : 12 * KA * delta ≤
      epsilonGuard B.sampleData.n / (p.1 : ℝ) := by
    apply (le_div_iff₀ hpR).2
    calc
      12 * KA * delta * (p.1 : ℝ) =
          (p.1 : ℝ) * (12 * KA * delta) := by ring
      _ ≤ 6 * guardSquarefreeError
          (rawCell P I B.sampleData.n c) (G B.sampleData.n).guards
            Kscore B.sampleData.n := hguardCell
      _ ≤ 6 * canonicalGuardSquarefreeError P I G Kscore
          B.sampleData.n := mul_le_mul_of_nonneg_left hcellToSum (by norm_num)
      _ = epsilonGuard B.sampleData.n := rfl
  calc
    |(B.cellMediumLaw xi c).covariance
        (fun m ↦ (valuation p.1 (m : ℕ) : ℝ))
        (fun m ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
      epsilonRaw B.sampleData.n / (p.1 : ℝ) +
        12 * KA * delta := by
      simpa only [KA, delta] using hcanonicalPrefix
    _ ≤ epsilonRaw B.sampleData.n / (p.1 : ℝ) +
        epsilonGuard B.sampleData.n / (p.1 : ℝ) :=
      add_le_add le_rfl hguardRow
    _ = epsilon B.sampleData.n / (p.1 : ℝ) := by
      dsimp only [epsilon]
      ring



end PaperBridgeFit.BridgeData

end

end Erdos390.Full.PaperCanonicalTiltedPrefixRows

end

universe u_1 u_2
theorem solution : Erdos390.RemainingAnalyticGoal004_003.{u_1, u_2} := by
  exact @Erdos390.Full.PaperCanonicalTiltedPrefixRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_tilted_valuation_prefix_rate_unrestricted
