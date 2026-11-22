-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_uniform_guardedRawCell_valuation_mean_profiles_paperRate_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:25:58.246029+00:00
-- url     : https://prove2.me/submissions/ecbcafc1-8fcb-4257-882d-8b0342d0ccbb

import Definitions.Def_erdos390_remaining_analytic_propositions_007
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_005
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_uniform_rawStructuredCell_valuation_mean_profile_paperRate_compact


section
theorem Erdos390.WholePaper.BankPaperRealization.exists_uniform_rawStructuredCell_valuation_mean_profile_paperRate : Erdos390.RemainingAnalyticGoal007_011 := @Erdos390.WholePaper.BankPaperRealization.exists_uniform_rawStructuredCell_valuation_mean_profile_paperRate_compact
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





end FiniteLogStieltjes

namespace GuardedUniformCell

open FiniteLogStieltjes

variable {Alpha : Type*} [DecidableEq Alpha]



/-- The corresponding expectation perturbation with the guard census
inserted.  Applied to a bounded truncated valuation, this is the exact guard
term in the pairwise component-mean comparison. -/
theorem exists_deleteGuards_expect_bound
    (S G : Finset Alpha) (hS : S.Nonempty)
    (score : S → ℝ) (Kscore : ℝ)
    (hscore : ∀ x, |score x| ≤ Kscore)
    (F : S → ℝ) {KF : ℝ} (hKF : 0 ≤ KF)
    (hF : ∀ x, |F x| ≤ KF)
    (hsmallCensus :
      Real.exp (2 * Kscore) * (G.card : ℝ) / (S.card : ℝ) ≤
        (1 : ℝ) / 2) :
    ∃ hsmall :
        ((uniformOnFinset S hS).exponentialTilt score).guardMass
          (guardSubtype S G) < 1,
      |(((uniformOnFinset S hS).exponentialTilt score).deleteGuards
          (guardSubtype S G) hsmall).expect F -
        ((uniformOnFinset S hS).exponentialTilt score).expect F| ≤
        4 * KF *
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
  have hraw := mu.abs_deleteGuards_expect_sub_le guards hsmall F hKF hF
  have hperturb := mu.guardPerturbation_le_four_mul_guardMass guards hhalf
  calc
    |(mu.deleteGuards guards hsmall).expect F - mu.expect F| ≤
      KF * mu.guardPerturbation guards := hraw
    _ ≤ KF * (4 * mu.guardMass guards) :=
      mul_le_mul_of_nonneg_left hperturb hKF
    _ ≤ KF * (4 * delta) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmass (by norm_num)) hKF
    _ = 4 * KF * delta := by ring

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





end PaperBridgeFit.BridgeData

end

end Erdos390.Full.PaperCanonicalTiltedPrefixRows

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosure -/
section


/-!
# Sharp valuation-rate ingredients for the smooth source

This file begins the analytic lift left explicit by
`BankPaperCanonicalSmoothSourceGuardedRateClosure`.

The first theorem below is the sharp un-tilted full-valuation profile for one
fixed raw structured cell.  It is obtained only from already proved inputs:

* the common `paperDivisibilityMain` law through `yNat n ^ 4`;
* the arbitrary-divisor reciprocal fallback;
* the finite prime-power tail identity; and
* the sharp conversion of the `yNat n ^ 4` tail to `1 / (p * L n)`.

No full-valuation comparison is assumed.
-/

open Filter Topology
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells
open Erdos390.Full.FiniteProbability
open Erdos390.Full.PrimePowerCovariance
open Erdos390.Full.PrimePowerCutoffCovariance
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.PaperMovingPrefixMarkedCell
open Erdos390.Full.PaperPrimePowerTailRate
open Erdos390.Full.PaperRawPrefixThirdCumulantFallback
open Erdos390.Full.PaperRawTiltedValuationMeanRows
open Erdos390.Full.LocalFugacityBounds
open Erdos390.Full.ValuationScoreDomination
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.GuardedUniformCell
open Erdos390.Full.GuardDeletionSquarefreeProfiles
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperCanonicalTiltedPrefixRows

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Fixed raw structured cells -/



/-- Fixed finitely many raw cells admit one common sharp valuation-profile
constant and one common threshold.  The Dickman main sum is independent of
the cell index, which is the essential input for the later barycentric
mixture. -/
theorem
    exists_uniform_fixedFinite_rawStructuredCell_valuation_mean_profiles_paperRate
    {CellIndex : Type*} [Fintype CellIndex] [Nonempty CellIndex]
    (H : CellIndex → Pattern) (A C : CellIndex → Real)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c)
    (W : Nat) (hW : 1 < W)
    (hHeadLe : ∀ c, ∀ q ∈ (H c).primes, q ≤ W) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {n p : Nat}, N₀ ≤ n → p ∈ primeBand n W →
        let Kcut := Nat.log p (yNat n ^ 4)
        ∀ c : CellIndex,
          let S := structuredCell (H c)
            (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
          ∃ hS : S.Nonempty,
            |(uniformOnFinset S hS).expect
                  (fun m ↦ valuation p (m : Nat)) -
              ∑ k ∈ positiveExponents Kcut,
                paperDivisibilityMain n (p ^ k)| ≤
              Cval / ((p : Real) * L n) := by
  classical
  have hcell : ∀ c : CellIndex,
      ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
        ∀ {n p : Nat}, N₀ ≤ n → p ∈ primeBand n W →
          let S := structuredCell (H c)
            (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
          let Kcut := Nat.log p (yNat n ^ 4)
          ∃ hS : S.Nonempty,
            |(uniformOnFinset S hS).expect
                  (fun m ↦ valuation p (m : Nat)) -
              ∑ k ∈ positiveExponents Kcut,
                paperDivisibilityMain n (p ^ k)| ≤
              Cval / ((p : Real) * L n) := by
    intro c
    exact
      exists_uniform_rawStructuredCell_valuation_mean_profile_paperRate
        (H c) (hA c) (hAC c) (hC c) W hW (hHeadLe c)
  choose Ccell hCcell Ncell hrate using hcell
  let Cval : Real := ∑ c : CellIndex, Ccell c
  let N₀ : Nat := 2 + ∑ c : CellIndex, Ncell c
  have hCcell0 (c : CellIndex) : 0 ≤ Ccell c := (hCcell c).le
  let c₀ : CellIndex := Classical.choice (inferInstance : Nonempty CellIndex)
  have hCval : 0 < Cval := by
    have hsingle : Ccell c₀ ≤ Cval := by
      dsimp only [Cval]
      exact Finset.single_le_sum
        (fun c _hc ↦ hCcell0 c) (Finset.mem_univ c₀)
    exact (hCcell c₀).trans_le hsingle
  refine ⟨Cval, hCval, N₀, ?_⟩
  intro n p hN hpBand
  dsimp only
  intro c
  have hNc : Ncell c ≤ n := by
    have hle : Ncell c ≤ N₀ := by
      dsimp only [N₀]
      have hsingle :
          Ncell c ≤ ∑ d : CellIndex, Ncell d :=
        Finset.single_le_sum
          (fun d _hd ↦ Nat.zero_le (Ncell d)) (Finset.mem_univ c)
      omega
    exact hle.trans hN
  have hraw := hrate c hNc hpBand
  rcases hraw with ⟨hS, hbound⟩
  refine ⟨hS, hbound.trans ?_⟩
  have hCcellLe : Ccell c ≤ Cval := by
    dsimp only [Cval]
    exact Finset.single_le_sum
      (fun d _hd ↦ hCcell0 d) (Finset.mem_univ c)
  have hden0 : 0 ≤ (p : Real) * L n := by
    exact mul_nonneg (by positivity) (L_pos (by omega)).le
  exact div_le_div_of_nonneg_right hCcellLe hden0

/-! ## Literal guard deletion -/

/-- Tilting by the identically-zero score does not change an expectation.
This small identity lets the general conditional-deletion theorem be used
without replacing the literal uniform laws by unnamed equivalent laws. -/
theorem finiteProbability_exponentialTilt_zero_expect
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (F : Omega → Real) :
    (mu.exponentialTilt (fun _ ↦ 0)).expect F = mu.expect F := by
  have hpartition :
      mu.expPartition (fun _ ↦ 0) = 1 := by
    unfold FiniteProbability.expPartition FiniteProbability.expect
    simp only [Real.exp_zero, mul_one]
    exact mu.mass_sum
  rw [mu.exponentialTilt_expect_eq, hpartition, div_one]
  apply congrArg mu.expect
  funext omega
  simp

/-- Quantitative deletion of a literal finset from an un-tilted uniform
law.  The conclusion is obtained from the general conditional-law theorem;
the surviving law is reindexed exactly as `uniformOnFinset (S \ G)`. -/
theorem
    abs_uniformOnFinset_sdiff_expect_sub_uniformOnFinset_expect_le
    (S G : Finset Nat) (hS : S.Nonempty) (hR : (S \ G).Nonempty)
    (F : Nat → Real) {KF : Real} (hKF : 0 ≤ KF)
    (hF : ∀ m ∈ S, |F m| ≤ KF)
    (hsmallCensus :
      (G.card : Real) / (S.card : Real) ≤ (1 : Real) / 2) :
    |(uniformOnFinset (S \ G) hR).expect (fun m ↦ F (m : Nat)) -
        (uniformOnFinset S hS).expect (fun m ↦ F (m : Nat))| ≤
      4 * KF * ((G.card : Real) / (S.card : Real)) := by
  let score : S → Real := fun _ ↦ 0
  have hscore : ∀ m : S, |score m| ≤ (0 : Real) := by
    intro m
    simp only [score, abs_zero, le_refl]
  have hFsub : ∀ m : S, |F (m : Nat)| ≤ KF := by
    intro m
    exact hF m m.property
  have hsmallCensus' :
      Real.exp (2 * (0 : Real)) * (G.card : Real) /
          (S.card : Real) ≤ (1 : Real) / 2 := by
    simpa using hsmallCensus
  obtain ⟨hsmall, hdiff⟩ :=
    GuardedUniformCell.exists_deleteGuards_expect_bound
      S G hS score 0 hscore (fun m : S ↦ F (m : Nat))
        hKF hFsub hsmallCensus'
  have hreindex :=
    deleteGuards_tilted_uniform_expect_remaining_eq
      S G hS hR score hsmall (fun m : S ↦ F (m : Nat))
  have hremainingZero :
      ((uniformOnFinset (S \ G) hR).exponentialTilt
          (fun z ↦ score (remainingEmbedding S G z))).expect
            (fun z ↦ F ((remainingEmbedding S G z : S) : Nat)) =
        (uniformOnFinset (S \ G) hR).expect
          (fun z ↦ F (z : Nat)) := by
    have hzero :=
      finiteProbability_exponentialTilt_zero_expect
        (uniformOnFinset (S \ G) hR) (fun z ↦ F (z : Nat))
    simpa only [score, remainingEmbedding_value] using hzero
  have hrawZero :
      ((uniformOnFinset S hS).exponentialTilt score).expect
          (fun m ↦ F (m : Nat)) =
        (uniformOnFinset S hS).expect (fun m ↦ F (m : Nat)) := by
    simpa only [score] using
      finiteProbability_exponentialTilt_zero_expect
        (uniformOnFinset S hS) (fun m ↦ F (m : Nat))
  rw [hreindex, hremainingZero, hrawZero] at hdiff
  simpa using hdiff

/-! ## The concrete guard ledger at the stronger `1 / L` rate -/

private theorem sharp_y_cube_div_nat_eq_inv_rpow
    {n : Nat} (hn : 0 < n) :
    y n ^ 3 / (n : Real) = 1 / (n : Real) ^ (1 / 3 : Real) := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hpow :
      ((n : Real) ^ (2 / 9 : Real)) ^ 3 *
          (n : Real) ^ (1 / 3 : Real) = (n : Real) := by
    calc
      ((n : Real) ^ (2 / 9 : Real)) ^ 3 *
          (n : Real) ^ (1 / 3 : Real) =
        (((n : Real) ^ (2 / 9 : Real) *
            (n : Real) ^ (2 / 9 : Real)) *
          ((n : Real) ^ (2 / 9 : Real) *
            (n : Real) ^ (1 / 3 : Real))) := by ring
      _ = (n : Real) ^ ((2 / 9 : Real) + 2 / 9) *
          (n : Real) ^ ((2 / 9 : Real) + 1 / 3) := by
        rw [Real.rpow_add hnR, Real.rpow_add hnR]
      _ = (n : Real) ^ (((2 / 9 : Real) + 2 / 9) +
          ((2 / 9 : Real) + 1 / 3)) := by
        rw [← Real.rpow_add hnR]
      _ = (n : Real) := by norm_num [Real.rpow_one]
  unfold y
  field_simp [(Real.rpow_pos_of_pos hnR (1 / 3 : Real)).ne', hnR.ne']
  nlinarith

private theorem sharp_census_mul_y_sq_expansion
    (Cprom Cbank n : Nat) (hn : 0 < n) :
    censusRatioMajorant Cprom Cbank n * y n ^ 2 =
      (Cprom : Real) * (1 / (n : Real) ^ (1 / 3 : Real)) +
        3 * (Cbank : Real) *
          (L n / (n : Real) ^ (1 / 3 : Real) +
            2 * (1 / (n : Real) ^ (1 / 3 : Real))) := by
  rw [censusRatioMajorant]
  rw [show
    (((Cprom : Real) + 3 * (Cbank : Real) * (L n + 2)) * y n /
        (n : Real)) * y n ^ 2 =
      ((Cprom : Real) + 3 * (Cbank : Real) * (L n + 2)) *
        (y n ^ 3 / (n : Real)) by ring]
  rw [sharp_y_cube_div_nat_eq_inv_rpow hn]
  ring

/-- The concrete reciprocal guard majorant is in fact `o(1 / L)`.
The older public theorem retained only the weaker moving-low
`o(1 / log L)` consequence. -/
theorem tendsto_censusRatioMajorant_mul_y_sq_mul_L_zero_sharp
    (Cprom Cbank : Nat) :
    Tendsto (fun n : Nat ↦
      censusRatioMajorant Cprom Cbank n * y n ^ 2 * L n)
      atTop (nhds 0) := by
  let a : Real := 1 / 3
  have ha : 0 < a := by norm_num [a]
  have hlog :
      Tendsto (fun n : Nat ↦ L n / (n : Real) ^ a)
        atTop (nhds 0) := by
    have hreal : Tendsto
        (fun x : Real ↦ Real.log x ^ (1 : Real) / x ^ a)
        atTop (nhds 0) :=
      (isLittleO_log_rpow_rpow_atTop (1 : Real) ha).tendsto_div_nhds_zero
    have hnat := hreal.comp tendsto_natCast_atTop_atTop
    apply hnat.congr'
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    simp only [Function.comp_apply, L, Real.rpow_one]
  have hlogSq :
      Tendsto (fun n : Nat ↦ L n ^ 2 / (n : Real) ^ a)
        atTop (nhds 0) := by
    have hreal : Tendsto
        (fun x : Real ↦ Real.log x ^ (2 : Real) / x ^ a)
        atTop (nhds 0) :=
      (isLittleO_log_rpow_rpow_atTop (2 : Real) ha).tendsto_div_nhds_zero
    have hnat := hreal.comp tendsto_natCast_atTop_atTop
    change Tendsto
      (fun n : Nat ↦ Real.log (n : Real) ^ (2 : Real) /
        (n : Real) ^ a) atTop (nhds 0) at hnat
    simpa [L, Real.rpow_natCast] using hnat
  let upper : Nat → Real := fun n ↦
    (Cprom : Real) * (L n / (n : Real) ^ a) +
      3 * (Cbank : Real) *
        (L n ^ 2 / (n : Real) ^ a +
          2 * (L n / (n : Real) ^ a))
  have hupper : Tendsto upper atTop (nhds 0) := by
    dsimp only [upper]
    simpa only [mul_zero, add_zero] using
      (hlog.const_mul (Cprom : Real)).add
        ((hlogSq.add (hlog.const_mul 2)).const_mul
          (3 * (Cbank : Real)))
  apply hupper.congr'
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  rw [sharp_census_mul_y_sq_expansion Cprom Cbank n hn]
  dsimp only [upper, a]
  ring

/-- Fixed multiplicative constants preserve the stronger concrete guard
rate. -/
theorem tendsto_guardRateMajorant_mul_L_zero_sharp
    (Cprom Cbank : Nat) (constant : Real) :
    Tendsto (fun n : Nat ↦ constant *
      (censusRatioMajorant Cprom Cbank n * y n ^ 2) * L n)
      atTop (nhds 0) := by
  have hc : Tendsto (fun _n : Nat ↦ constant)
      atTop (nhds constant) := tendsto_const_nhds
  have h := hc.mul
    (tendsto_censusRatioMajorant_mul_y_sq_mul_L_zero_sharp
      Cprom Cbank)
  simpa only [mul_zero, mul_assoc] using h

/-- The family-aggregated literal guard error is also `o(1 / L)`. -/
theorem tendsto_canonicalGuardSquarefreeError_mul_L_zero_sharp
    {Head : Type*} [Fintype Head]
    (P : Head → Pattern) (I : PaperGuardCensus.PhysicalIntervals)
    {Cprom Cbank : Nat}
    (G : ∀ n, PaperGuardCensus.Ledger n Cprom Cbank) (Kscore : Real) :
    Tendsto (fun n : Nat ↦
      GuardSquarefreeErrorRate.canonicalGuardSquarefreeError
          P I G Kscore n * L n)
      atTop (nhds 0) := by
  have hL0 : ∀ᶠ n : Nat in atTop, 0 ≤ L n := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact Real.log_nonneg (by exact_mod_cast hn)
  have hcell (c : PaperBridgeFit.Cell Head) :
      Tendsto (fun n : Nat ↦
        GuardDeletionSquarefreeProfiles.guardSquarefreeError
            (PaperGuardCensus.rawCell P I n c) (G n).guards
              Kscore n * L n)
        atTop (nhds 0) := by
    let constant := 4 * Real.exp (2 * Kscore) /
      PaperScaleMarkedCell.paperCellDensity (P c.1)
        (I.lower c.2) (I.upper c.2)
    have hupper :=
      tendsto_guardRateMajorant_mul_L_zero_sharp
        Cprom Cbank constant
    have hdensity := PaperGuardCensus.eventually_rawCell_density P I
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards [hL0] with n hLn
      exact mul_nonneg
        (GuardDeletionSquarefreeProfiles.guardSquarefreeError_nonneg
          _ _ _ _) hLn
    · filter_upwards [hdensity, Filter.eventually_gt_atTop 0, hL0]
        with n hdens hn hLn
      have hguard :=
        GuardSquarefreeErrorRate.guardSquarefreeError_rawCell_le_rateMajorant
          P I (G n) c (by omega : 1 ≤ n) (hdens c) Kscore
      have hguard' :
          GuardDeletionSquarefreeProfiles.guardSquarefreeError
              (PaperGuardCensus.rawCell P I n c) (G n).guards
                Kscore n ≤
            constant *
              (censusRatioMajorant Cprom Cbank n * y n ^ 2) := by
        simpa only [constant] using hguard
      exact mul_le_mul_of_nonneg_right hguard' hLn
  have hsum := tendsto_finset_sum
    (Finset.univ : Finset (PaperBridgeFit.Cell Head))
    (fun c _hc ↦ hcell c)
  have hsum0 : Tendsto (fun n : Nat ↦
      ∑ c : PaperBridgeFit.Cell Head,
        GuardDeletionSquarefreeProfiles.guardSquarefreeError
            (PaperGuardCensus.rawCell P I n c) (G n).guards
              Kscore n * L n)
      atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using hsum
  apply hsum0.congr'
  filter_upwards with n
  unfold GuardSquarefreeErrorRate.canonicalGuardSquarefreeError
  rw [Finset.sum_mul]

/-- After deletion of the concrete canonical guard ledger, every fixed
head/physical cell retains the same common full-valuation profile with an
explicit `1 / (p * L)` error.  This is the sharp un-tilted counterpart of
the older tilted `epsilon(n) / p` component theorem. -/
theorem
    exists_uniform_guardedRawCell_valuation_mean_profiles_paperRate
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (W : Nat) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (P h).primes, q ≤ W) :
    ∃ Cval : Real, 0 < Cval ∧ ∃ N₀ : Nat,
      ∀ {n p : Nat}, N₀ ≤ n → p ∈ primeBand n W →
        let Kcut := Nat.log p (yNat n ^ 4)
        ∀ c : Cell Head,
          ∀ hremaining :
            (rawCell P I n c \ (G n).guards).Nonempty,
            |(uniformOnFinset
                  (rawCell P I n c \ (G n).guards) hremaining).expect
                  (fun m ↦ valuation p (m : Nat)) -
              ∑ k ∈ positiveExponents Kcut,
                paperDivisibilityMain n (p ^ k)| ≤
              Cval / ((p : Real) * L n) := by
  let H : Cell Head → Pattern := fun c ↦ P c.1
  let Alower : Cell Head → Real := fun c ↦ I.lower c.2
  let Cupper : Cell Head → Real := fun c ↦ I.upper c.2
  obtain ⟨Craw, hCraw, Nraw, hraw⟩ :=
    exists_uniform_fixedFinite_rawStructuredCell_valuation_mean_profiles_paperRate
      H Alower Cupper
      (fun c ↦ I.lower_pos c.2)
      (fun c ↦ I.lower_lt_upper c.2)
      (fun c ↦ (I.lower_pos c.2).trans (I.lower_lt_upper c.2))
      W hW (fun c ↦ hHeadLe c.1)
  have hsmallEvent :=
    eventually_exp_two_mul_guardRatio_rawCell_le_half
      P I Cprom Cbank G 0
  have henvEvent :=
    eventually_valuationEnvelope_bounds (Head := Head) I W hW
  have hrowEnvEvent :=
    eventually_bandPrime_mul_valuationEnvelope_le_yNat_sq
      (Head := Head) I W hW
  have hguardRate :=
    tendsto_canonicalGuardSquarefreeError_mul_L_zero_sharp
      P I G 0
  have hguardSmall : ∀ᶠ n : Nat in atTop,
      canonicalGuardSquarefreeError P I G 0 n * L n ≤ 1 :=
    hguardRate.eventually (eventually_le_nhds (by norm_num))
  have hAll : ∀ᶠ n : Nat in atTop,
      (∀ c : Cell Head,
        ((G n).guards.card : Real) /
          ((rawCell P I n c).card : Real) ≤ (1 : Real) / 2) ∧
      (∀ c : Cell Head,
        0 ≤ valuationEnvelope I n W c ∧
          valuationEnvelope I n W c ≤
            (2 / Real.log (W : Real)) * L n) ∧
      (∀ (c : Cell Head) (p : BandPrime n W),
        (p.1 : Real) * valuationEnvelope I n W c ≤
          (yNat n : Real) ^ 2) ∧
      canonicalGuardSquarefreeError P I G 0 n * L n ≤ 1 ∧
      1 < n := by
    filter_upwards [hsmallEvent, henvEvent, hrowEnvEvent, hguardSmall,
      Filter.eventually_gt_atTop 1] with
      n hsmallN henvN hrowEnvN hguardN hn
    have hsmallN' : ∀ c : Cell Head,
        ((G n).guards.card : Real) /
          ((rawCell P I n c).card : Real) ≤ (1 : Real) / 2 := by
      intro c
      have hc := hsmallN c
      norm_num at hc
      simpa using hc
    exact ⟨hsmallN', henvN, hrowEnvN, hguardN, hn⟩
  obtain ⟨Nevent, hNevent⟩ := Filter.eventually_atTop.mp hAll
  let Cval : Real := Craw + 2
  have hCval : 0 < Cval := by
    dsimp only [Cval]
    linarith
  refine ⟨Cval, hCval, max Nraw Nevent, ?_⟩
  intro n p hN hpBand
  dsimp only
  intro c hremaining
  have hNraw : Nraw ≤ n := by omega
  have hNeventBound : Nevent ≤ n := by omega
  obtain ⟨hsmallN, henvN, hrowEnvN, hguardN, hn⟩ :=
    hNevent n hNeventBound
  have hp := prime_of_mem_primeBand hpBand
  have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
  have hL : 0 < L n := L_pos hn
  have hrawCell := hraw (n := n) (p := p) hNraw hpBand c
  rcases hrawCell with ⟨hS, hrawBound⟩
  let S := rawCell P I n c
  let KA := valuationEnvelope I n W c
  have hKA : 0 ≤ KA := by
    exact (henvN c).1
  have hvaluation : ∀ m ∈ S, |valuation p m| ≤ KA := by
    intro m hm
    rw [abs_of_nonneg (valuation_nonneg p m)]
    let pBand : BandPrime n W := ⟨p, hpBand⟩
    let mRaw : rawCell P I n c :=
      ⟨m, by simpa only [S] using hm⟩
    exact (rawCell_valuation_le_total P I pBand c mRaw).trans
      (by
        simpa only [KA] using
          rawCell_totalBandValuation_le P I hW c mRaw)
  have hdelete :=
    abs_uniformOnFinset_sdiff_expect_sub_uniformOnFinset_expect_le
      S (G n).guards hS
        (by simpa only [S] using hremaining)
        (fun m ↦ valuation p m) hKA
        (by
          intro m hm
          simpa only [S] using hvaluation m hm)
        (by simpa only [S] using hsmallN c)
  let guardError :=
    guardSquarefreeError S (G n).guards 0 n
  have hratio0 : 0 ≤
      ((G n).guards.card : Real) / (S.card : Real) := by
    positivity
  have hrowEnv :
      (p : Real) * KA ≤ (yNat n : Real) ^ 2 := by
    let pBand : BandPrime n W := ⟨p, hpBand⟩
    simpa only [KA] using hrowEnvN c pBand
  have hguardCell :
      (p : Real) *
          (4 * KA *
            (((G n).guards.card : Real) / (S.card : Real))) ≤
        2 * guardError := by
    unfold guardError guardSquarefreeError
    norm_num
    calc
      (p : Real) *
          (4 * KA *
            (((G n).guards.card : Real) / (S.card : Real))) =
        4 * ((p : Real) * KA) *
          (((G n).guards.card : Real) / (S.card : Real)) := by ring
      _ ≤ 4 * (yNat n : Real) ^ 2 *
          (((G n).guards.card : Real) / (S.card : Real)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrowEnv (by norm_num)) hratio0
      _ = 2 *
          (2 * (((G n).guards.card : Real) / (S.card : Real)) *
            (yNat n : Real) ^ 2) := by ring
  have hguardToCanonical :
      guardError ≤ canonicalGuardSquarefreeError P I G 0 n := by
    unfold canonicalGuardSquarefreeError
    exact Finset.single_le_sum
      (fun d _hd ↦ guardSquarefreeError_nonneg
        (rawCell P I n d) (G n).guards 0 n)
      (Finset.mem_univ c)
  have hcanonicalRate :
      canonicalGuardSquarefreeError P I G 0 n ≤ 1 / L n := by
    apply (le_div_iff₀ hL).2
    simpa only [one_mul] using hguardN
  have hdeleteRate :
      4 * KA * (((G n).guards.card : Real) / (S.card : Real)) ≤
        2 / ((p : Real) * L n) := by
    have hdivp :
        4 * KA * (((G n).guards.card : Real) / (S.card : Real)) ≤
          (2 / L n) / (p : Real) := by
      apply (le_div_iff₀ hpR).2
      calc
        (4 * KA *
            (((G n).guards.card : Real) / (S.card : Real))) *
              (p : Real) =
            (p : Real) *
              (4 * KA *
                (((G n).guards.card : Real) / (S.card : Real))) := by ring
        _ ≤ 2 * guardError := hguardCell
        _ ≤ 2 * canonicalGuardSquarefreeError P I G 0 n :=
          mul_le_mul_of_nonneg_left hguardToCanonical (by norm_num)
        _ ≤ 2 * (1 / L n) :=
          mul_le_mul_of_nonneg_left hcanonicalRate (by norm_num)
        _ = 2 / L n := by ring
    calc
      4 * KA * (((G n).guards.card : Real) / (S.card : Real)) ≤
          (2 / L n) / (p : Real) := hdivp
      _ = 2 / ((p : Real) * L n) := by
        field_simp [hpR.ne', hL.ne']
  have hdeleteBound :
      |(uniformOnFinset
            (rawCell P I n c \ (G n).guards) hremaining).expect
            (fun m ↦ valuation p (m : Nat)) -
        (uniformOnFinset (rawCell P I n c) hS).expect
            (fun m ↦ valuation p (m : Nat))| ≤
          2 / ((p : Real) * L n) := by
    have hrawDelete :
        |(uniformOnFinset (S \ (G n).guards)
              (by simpa only [S] using hremaining)).expect
              (fun m ↦ valuation p (m : Nat)) -
          (uniformOnFinset S hS).expect
              (fun m ↦ valuation p (m : Nat))| ≤
            4 * KA *
              (((G n).guards.card : Real) / (S.card : Real)) := by
      simpa only [S] using hdelete
    simpa only [S] using hrawDelete.trans hdeleteRate
  let Kcut := Nat.log p (yNat n ^ 4)
  let mainSum := ∑ k ∈ positiveExponents Kcut,
    paperDivisibilityMain n (p ^ k)
  change
    |(uniformOnFinset
          (rawCell P I n c \ (G n).guards) hremaining).expect
          (fun m ↦ valuation p (m : Nat)) - mainSum| ≤
      Cval / ((p : Real) * L n)
  calc
    |(uniformOnFinset
          (rawCell P I n c \ (G n).guards) hremaining).expect
          (fun m ↦ valuation p (m : Nat)) - mainSum| ≤
      |(uniformOnFinset
            (rawCell P I n c \ (G n).guards) hremaining).expect
            (fun m ↦ valuation p (m : Nat)) -
        (uniformOnFinset (rawCell P I n c) hS).expect
            (fun m ↦ valuation p (m : Nat))| +
      |(uniformOnFinset (rawCell P I n c) hS).expect
            (fun m ↦ valuation p (m : Nat)) - mainSum| := by
        have htri := abs_add_le
          ((uniformOnFinset
              (rawCell P I n c \ (G n).guards) hremaining).expect
              (fun m ↦ valuation p (m : Nat)) -
            (uniformOnFinset (rawCell P I n c) hS).expect
              (fun m ↦ valuation p (m : Nat)))
          ((uniformOnFinset (rawCell P I n c) hS).expect
              (fun m ↦ valuation p (m : Nat)) - mainSum)
        simpa only [sub_add_sub_cancel] using htri
    _ ≤ 2 / ((p : Real) * L n) +
        Craw / ((p : Real) * L n) :=
      add_le_add hdeleteBound (by
        simpa only [H, Alower, Cupper, Kcut, mainSum, rawCell] using
          hrawBound)
    _ = Cval / ((p : Real) * L n) := by
      dsimp only [Cval]
      ring



end BankPaperRealization

end

end Erdos390.WholePaper

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal007_005.{u_1} := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_uniform_guardedRawCell_valuation_mean_profiles_paperRate
