-- Prove2me | solution 1 for Erdos390.Full.FriableAsymptotic.exists_uniform_friableCount_dickman_bound
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T14:50:40.822212+00:00
-- url     : https://prove2.me/submissions/0e94c00c-b998-4ac7-9fe2-ebd0f5684cdc

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Theorems.Thm_Erdos390_Full_FriableAsymptotic_dickmanWeight_pnt_bound

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









theorem dickmanContinuousWeight_nat (X m : ℕ) :
    dickmanContinuousWeight (X : ℝ) (m : ℝ) =
      dickmanThetaWeight X m := by
  simp only [dickmanContinuousWeight, dickmanThetaWeight,
    dickmanPrimeSummand]

/-- The continuous Dickman test weight is continuous away from the two
irrelevant singular points `0` and `1`. -/
theorem continuousOn_dickmanContinuousWeight (X : ℝ) :
    ContinuousOn (dickmanContinuousWeight X) (Set.Ioi (1 : ℝ)) := by
  intro t ht
  rw [Set.mem_Ioi] at ht
  have ht0 : t ≠ 0 := by linarith [ht]
  have ht1 : t ≠ 1 := by linarith [ht]
  have hlog_ne : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht]) ht1
  have hlog : ContinuousAt Real.log t := Real.continuousAt_log ht0
  have hq : ContinuousAt
      (fun u : ℝ => Real.log X / Real.log u - 1) t :=
    (continuousAt_const.div hlog hlog_ne).sub continuousAt_const
  have hrho : ContinuousAt
      (fun u : ℝ => rho (Real.log X / Real.log u - 1)) t :=
    continuous_rho.continuousAt.comp hq
  have hmain : ContinuousAt
      (fun u : ℝ => X / u * rho (Real.log X / Real.log u - 1)) t :=
    (continuousAt_const.div continuousAt_id ht0).mul hrho
  exact (hmain.div hlog hlog_ne).continuousWithinAt

/-- Pointwise derivative identity behind the de Bruijn integral. -/
theorem hasDerivAt_dickmanAntiderivative (X t : ℝ) (ht : 1 < t)
    (hq1 : 1 < Real.log X / Real.log t)
    (hq6 : Real.log X / Real.log t ≤ 6) :
    HasDerivAt (dickmanAntiderivative X)
      (dickmanContinuousWeight X t) t := by
  have ht0 : t ≠ 0 := by linarith
  have htlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  let q : ℝ → ℝ := fun s => Real.log X / Real.log s
  have hq : HasDerivAt q
      (-(Real.log X) / (t * (Real.log t) ^ 2)) t := by
    have hraw := (hasDerivAt_const t (Real.log X)).div
      (Real.hasDerivAt_log ht0) htlog
    convert hraw using 1
    field_simp
    ring
  have hrho := (hasDerivAt_rho hq1 hq6).comp t hq
  have hmul := (hasDerivAt_const t X).mul hrho
  convert hmul using 1
  unfold dickmanContinuousWeight
  dsimp [q] at hmul ⊢
  have hq0 : Real.log X / Real.log t ≠ 0 := by linarith
  have hlogX : Real.log X ≠ 0 := by
    intro hzero
    apply hq0
    rw [hzero, zero_div]
  field_simp [hlogX, htlog, ht0]
  ring



/-- Against a prime point mass, the factor `log p` in `θ` cancels exactly.
Thus the weighted Stieltjes sum is literally the desired Dickman prime sum,
not merely an approximation. -/
theorem primeThetaWeightedInterval_dickman (X : ℕ) {z y : ℕ} :
    primeThetaWeightedInterval (dickmanThetaWeight X) z y =
      ∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
        dickmanPrimeSummand X p := by
  rw [primeThetaWeightedInterval]
  apply Finset.sum_congr rfl
  intro p hp
  have hpprime : p.Prime := by
    exact Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast hpprime.pos) (by exact_mod_cast hpprime.ne_one)
  rw [dickmanThetaWeight]
  exact div_mul_cancel₀ _ hlog















/-- Exact Dickman formula on the initial face `u ≤ 1`.  The only discrepancy
between the real endpoint and the count is therefore the explicit floor used
to create `X`; no analytic error occurs here. -/
theorem friableCount_eq_dickman_initial {X y : ℕ} (hX : 0 < X)
    (hy : 1 < y) (hXy : X ≤ y) :
    (friableCount X y : ℝ) = (X : ℝ) * rho (dickmanU X y) := by
  rw [friableCount_eq_self hXy, rho_eq_one_of_le_one
    (dickmanU_le_one hX hy hXy)]
  ring



private theorem mem_smooth_succ_not_smooth_iff_dvd {p m : ℕ}
    (hp : p.Prime) (hm : m ∈ Nat.smoothNumbers (p + 1)) :
    m ∉ Nat.smoothNumbers p ↔ p ∣ m := by
  rw [Nat.mem_smoothNumbers'] at hm
  constructor
  · intro hnot
    by_contra hpdvd
    apply hnot
    rw [Nat.mem_smoothNumbers']
    intro q hq hqdiv
    have hqsucc : q < p + 1 := hm q hq hqdiv
    have hqne : q ≠ p := by
      intro hqp
      exact hpdvd (hqp ▸ hqdiv)
    omega
  · intro hpdiv hsmooth
    rw [Nat.mem_smoothNumbers'] at hsmooth
    exact (Nat.lt_irrefl p) (hsmooth p hp hpdiv)

theorem primeMultipleCell_card (X : ℕ) {p : ℕ} (hp : p.Prime) :
    (primeMultipleCell X p).card = friableCount (X / p) p := by
  classical
  apply Finset.card_bij (fun m _ => m / p)
  · intro m hm
    rw [primeMultipleCell, Finset.mem_filter,
      Nat.mem_smoothNumbersUpTo] at hm
    rw [Nat.mem_smoothNumbersUpTo]
    refine ⟨?_, Nat.mem_smoothNumbers_of_dvd hm.1.2 (Nat.div_dvd_of_dvd hm.2)⟩
    apply (Nat.le_div_iff_mul_le hp.pos).mpr
    simpa [Nat.div_mul_cancel hm.2] using hm.1.1
  · intro m₁ hm₁ m₂ hm₂ heq
    rw [primeMultipleCell, Finset.mem_filter] at hm₁ hm₂
    calc
      m₁ = m₁ / p * p := (Nat.div_mul_cancel hm₁.2).symm
      _ = m₂ / p * p := by rw [heq]
      _ = m₂ := Nat.div_mul_cancel hm₂.2
  · intro k hk
    rw [Nat.mem_smoothNumbersUpTo] at hk
    refine ⟨k * p, ?_, ?_⟩
    · rw [primeMultipleCell, Finset.mem_filter,
        Nat.mem_smoothNumbersUpTo]
      refine ⟨⟨?_, Nat.mul_mem_smoothNumbers hk.2 ?_⟩, by simp⟩
      · exact (Nat.le_div_iff_mul_le hp.pos).mp hk.1
      · exact Nat.mem_smoothNumbers_of_lt hp.pos (by omega)
    · exact Nat.mul_div_left k hp.pos

/-- Exact one-prime Buchstab recursion.  The first term excludes `p`; the
second term divides the newly admitted multiples of `p` by `p`.  Repeatedly
applying this identity is the discrete arithmetic induction underlying the
finite-range de Bruijn argument. -/
theorem friableCount_prime_step (X : ℕ) {p : ℕ} (hp : p.Prime) :
    friableCount X p =
      friableCount X (p - 1) + friableCount (X / p) p := by
  classical
  let A := Nat.smoothNumbersUpTo X (p + 1)
  let P : ℕ → Prop := fun m => m ∈ Nat.smoothNumbers p
  have hpartition := Finset.card_filter_add_card_filter_not (s := A) P
  have hbelow : A.filter P = Nat.smoothNumbersUpTo X p := by
    ext m
    simp only [A, P, Finset.mem_filter, Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨⟨hmX, hm⟩, hmp⟩
      exact ⟨hmX, hmp⟩
    · rintro ⟨hmX, hmp⟩
      exact ⟨⟨hmX, Nat.smoothNumbers_mono (by omega) hmp⟩, hmp⟩
  have hnew : A.filter (fun m => ¬P m) = primeMultipleCell X p := by
    ext m
    simp only [A, P, primeMultipleCell, Finset.mem_filter,
      Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨⟨hmX, hm⟩, hn⟩
      exact ⟨⟨hmX, hm⟩, (mem_smooth_succ_not_smooth_iff_dvd hp hm).mp hn⟩
    · rintro ⟨⟨hmX, hm⟩, hpdiv⟩
      exact ⟨⟨hmX, hm⟩, (mem_smooth_succ_not_smooth_iff_dvd hp hm).mpr hpdiv⟩
  rw [hbelow, hnew, primeMultipleCell_card X hp] at hpartition
  have hpone : 1 ≤ p := hp.one_le
  simpa [friableCount, Nat.sub_add_cancel hpone, A] using hpartition.symm

/-- At a composite cutoff no new smooth numbers appear. -/
theorem friableCount_composite_step (X : ℕ) {k : ℕ} (hk : ¬k.Prime) :
    friableCount X k = friableCount X (k - 1) := by
  by_cases hk0 : k = 0
  · subst k
    simp [friableCount]
  have hkone : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  rw [friableCount, friableCount, Nat.sub_add_cancel hkone]
  unfold Nat.smoothNumbersUpTo
  congr 1
  ext m
  simp only [Finset.mem_filter, Nat.smoothNumbers_succ hk]

private theorem friableCount_cutoff_zero {X : ℕ} (hX : 0 < X) :
    friableCount X 0 = 1 := by
  have hset : Nat.smoothNumbersUpTo X 1 = {1} := by
    ext m
    rw [Nat.mem_smoothNumbersUpTo, Nat.smoothNumbers_one]
    simp only [Set.mem_singleton_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨hmX, rfl⟩
      rfl
    · rintro rfl
      exact ⟨hX, rfl⟩
  rw [friableCount, hset]
  simp

/-- Exact largest-prime-factor recursion

`\Psi(X,y) = 1 + \sum_{p \le y} \Psi(\lfloor X/p\rfloor,p)`.

The identity follows here from the one-prime step and therefore does not need
an independently postulated greatest-prime-factor decomposition.  This is the
finite recurrence to which prime Stieltjes summation is applied in the
de Bruijn induction. -/
theorem friableCount_largest_prime (X y : ℕ) (hX : 0 < X) :
    friableCount X y =
      1 + ∑ p ∈ (y + 1).primesBelow, friableCount (X / p) p := by
  induction y with
  | zero =>
      rw [friableCount_cutoff_zero hX]
      simp [Nat.primesBelow]
  | succ y ih =>
      by_cases hp : (y + 1).Prime
      · rw [friableCount_prime_step X hp]
        have hsub : y + 1 - 1 = y := by omega
        have hprimes : (y + 1 + 1).primesBelow =
            insert (y + 1) (y + 1).primesBelow := by
          rw [Nat.primesBelow_succ, if_pos hp]
        rw [hsub, ih, hprimes,
          Finset.sum_insert (Nat.notMem_primesBelow (y + 1))]
        omega
      · rw [friableCount_composite_step X hp]
        have hsub : y + 1 - 1 = y := by omega
        have hprimes : (y + 1 + 1).primesBelow = (y + 1).primesBelow := by
          rw [Nat.primesBelow_succ, if_neg hp]
        rw [hsub, ih, hprimes]

/-- Truncated largest-prime recursion.  This is the induction-friendly form:
choosing `z` so that `log X / log z` is an integer puts the first term on the
previous Dickman step, while every quotient in the prime interval has a
strictly smaller Dickman coordinate. -/
theorem friableCount_prime_interval (X : ℕ) {z y : ℕ} (hX : 0 < X)
    (hzy : z ≤ y) :
    friableCount X y = friableCount X z +
      ∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
        friableCount (X / p) p := by
  have hsubset : (z + 1).primesBelow ⊆ (y + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsum :
      (∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
          friableCount (X / p) p) +
        ∑ p ∈ (z + 1).primesBelow, friableCount (X / p) p =
          ∑ p ∈ (y + 1).primesBelow, friableCount (X / p) p := by
    simpa only using
      (Finset.sum_sdiff (f := fun p => friableCount (X / p) p) hsubset)
  rw [friableCount_largest_prime X y hX,
    friableCount_largest_prime X z hX]
  omega

/-! ## Explicit oscillation and Riemann error for the Dickman weight -/


open DickmanBasic





theorem deriv_invMulLog {t : ℝ} (ht : t ≠ 0)
    (hlog : Real.log t ≠ 0) :
    HasDerivAt invMulLog
      (-(Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) t := by
  unfold invMulLog
  have hden : HasDerivAt (fun s : ℝ => s * Real.log s)
      (Real.log t + 1) t := by
    simpa [ht] using (hasDerivAt_id t).mul (Real.hasDerivAt_log ht)
  have hraw := (hasDerivAt_const t (1 : ℝ)).div hden (mul_ne_zero ht hlog)
  convert hraw using 1
  field_simp [ht, hlog]
  ring

theorem deriv_logRatio (X : ℝ) {t : ℝ} (ht : t ≠ 0)
    (hlog : Real.log t ≠ 0) :
    HasDerivAt (logRatio X)
      (-(Real.log X) / (t * (Real.log t) ^ 2)) t := by
  unfold logRatio
  have hraw := (hasDerivAt_const t (Real.log X)).div
    (Real.hasDerivAt_log ht) hlog
  convert hraw using 1
  field_simp [ht, hlog]
  ring

theorem inv_deriv_bound {k : ℕ} (hk : 2 ≤ k) {t : ℝ}
    (ht : (k : ℝ) ≤ t) :
    |-(Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)| ≤
      6 / (k : ℝ) ^ 2 := by
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkt : (2 : ℝ) ≤ t := hkreal.trans ht
  have htpos : 0 < t := by linarith
  have hkposNat : 0 < k := lt_of_lt_of_le (by norm_num : 0 < 2) hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hkposNat
  have hlog : (1 / 2 : ℝ) ≤ Real.log t := by
    have hlogmono : Real.log 2 ≤ Real.log t := by
      apply Real.log_le_log
      · norm_num
      · exact hkt
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log t := by linarith
  rw [abs_div, abs_neg, abs_of_nonneg (by positivity : 0 ≤ Real.log t + 1),
    abs_mul]
  simp only [abs_pow, abs_of_pos htpos, abs_of_pos hlogpos]
  have hpoly : (Real.log t + 1) / (Real.log t) ^ 2 ≤ 6 := by
    apply (div_le_iff₀ (sq_pos_of_pos hlogpos)).2
    nlinarith [sq_nonneg (Real.log t - 1 / 2)]
  calc
    (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) =
        ((Real.log t + 1) / Real.log t ^ 2) / t ^ 2 := by field_simp
    _ ≤ 6 / t ^ 2 := by
      exact div_le_div_of_nonneg_right hpoly (sq_nonneg t)
    _ ≤ 6 / (k : ℝ) ^ 2 := by
      gcongr

theorem logRatio_deriv_bound (X : ℝ) (hX : 1 ≤ X)
    {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : (k : ℝ) ≤ t) :
    |-(Real.log X) / (t * (Real.log t) ^ 2)| ≤
      4 * Real.log X / (k : ℝ) := by
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkt : (2 : ℝ) ≤ t := hkreal.trans ht
  have htpos : 0 < t := by linarith
  have hkposNat : 0 < k := lt_of_lt_of_le (by norm_num : 0 < 2) hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hkposNat
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlog : (1 / 2 : ℝ) ≤ Real.log t := by
    have hlogmono : Real.log 2 ≤ Real.log t := by
      apply Real.log_le_log
      · norm_num
      · exact hkt
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log t := by linarith
  rw [abs_div, abs_neg, abs_of_nonneg hlogX, abs_mul,
    abs_of_pos htpos, abs_pow, abs_of_pos hlogpos]
  have hlogsq : (1 / 4 : ℝ) ≤ Real.log t ^ 2 := by nlinarith
  apply (div_le_div_iff₀ (mul_pos htpos (sq_pos_of_pos hlogpos)) hkpos).2
  have hden1 : t * (1 / 4 : ℝ) ≤ t * Real.log t ^ 2 :=
    mul_le_mul_of_nonneg_left hlogsq htpos.le
  have hden : (k : ℝ) ≤ 4 * (t * Real.log t ^ 2) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hden hlogX]

theorem invMulLog_cell_lipschitz {k : ℕ} (hk : 2 ≤ k)
    {s t : ℝ} (hs : s ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
    |invMulLog s - invMulLog t| ≤
      (6 / (k : ℝ) ^ 2) * |s - t| := by
  have hdiff (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      DifferentiableAt ℝ invMulLog u := by
    have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hu2 : (2 : ℝ) ≤ u := hkreal.trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    exact (deriv_invMulLog hu0 hlogu).differentiableAt
  have hbound (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      ‖deriv invMulLog u‖ ≤ 6 / (k : ℝ) ^ 2 := by
    have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hu2 : (2 : ℝ) ≤ u := hkreal.trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    rw [(deriv_invMulLog hu0 hlogu).deriv, Real.norm_eq_abs]
    exact inv_deriv_bound hk hu.1
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_Icc (k : ℝ) (k + 1 : ℕ)) ht hs

theorem logRatio_cell_lipschitz (X : ℝ) (hX : 1 ≤ X)
    {k : ℕ} (hk : 2 ≤ k)
    {s t : ℝ} (hs : s ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
    |logRatio X s - logRatio X t| ≤
      (4 * Real.log X / (k : ℝ)) * |s - t| := by
  have hdiff (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      DifferentiableAt ℝ (logRatio X) u := by
    have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hu2 : (2 : ℝ) ≤ u := hkreal.trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    exact (deriv_logRatio X hu0 hlogu).differentiableAt
  have hbound (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      ‖deriv (logRatio X) u‖ ≤ 4 * Real.log X / (k : ℝ) := by
    have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hu2 : (2 : ℝ) ≤ u := hkreal.trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    rw [(deriv_logRatio X hu0 hlogu).deriv, Real.norm_eq_abs]
    exact logRatio_deriv_bound X hX hk hu.1
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_Icc (k : ℝ) (k + 1 : ℕ)) ht hs

theorem invMulLog_bound {k : ℕ} (hk : 2 ≤ k) {t : ℝ}
    (ht : (k : ℝ) ≤ t) :
    0 ≤ invMulLog t ∧ invMulLog t ≤ 2 / (k : ℝ) := by
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkt : (2 : ℝ) ≤ t := hkreal.trans ht
  have htpos : 0 < t := by linarith
  have hkposNat : 0 < k := lt_of_lt_of_le (by norm_num : 0 < 2) hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hkposNat
  have hlog : (1 / 2 : ℝ) ≤ Real.log t := by
    have hlogmono : Real.log 2 ≤ Real.log t := by
      apply Real.log_le_log
      · norm_num
      · exact hkt
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log t := by linarith
  constructor
  · unfold invMulLog
    positivity
  · unfold invMulLog
    apply (div_le_iff₀ (mul_pos htpos hlogpos)).2
    rw [show 2 / (k : ℝ) * (t * Real.log t) =
      (2 * (t * Real.log t)) / (k : ℝ) by ring]
    apply (le_div_iff₀ hkpos).2
    have hprod : t * (1 / 2 : ℝ) ≤ t * Real.log t :=
      mul_le_mul_of_nonneg_left hlog htpos.le
    nlinarith

theorem rho_logRatio_lipschitz (X s t : ℝ)
    (hs5 : logRatio X s - 1 ≤ 5)
    (ht5 : logRatio X t - 1 ≤ 5) :
    |rho (logRatio X s - 1) - rho (logRatio X t - 1)| ≤
      |logRatio X s - logRatio X t| := by
  by_cases hst : logRatio X t - 1 ≤ logRatio X s - 1
  · have h := rho_lipschitz_of_le_five hst hs5
    calc
      |rho (logRatio X s - 1) - rho (logRatio X t - 1)| ≤
          (logRatio X s - 1) - (logRatio X t - 1) := h
      _ = logRatio X s - logRatio X t := by ring
      _ = |logRatio X s - logRatio X t| := by
        rw [abs_of_nonneg (by linarith)]
  · have h := rho_lipschitz_of_le_five (le_of_not_ge hst) ht5
    rw [abs_sub_comm]
    calc
      |rho (logRatio X t - 1) - rho (logRatio X s - 1)| ≤
          (logRatio X t - 1) - (logRatio X s - 1) := h
      _ = logRatio X t - logRatio X s := by ring
      _ = |logRatio X t - logRatio X s| := by
        rw [abs_of_nonneg (by linarith)]
      _ = |logRatio X s - logRatio X t| := abs_sub_comm _ _

theorem dickmanContinuousWeight_cell_lipschitz (X : ℝ) (hX : 1 ≤ X)
    {k : ℕ} (hk : 2 ≤ k) {s t : ℝ}
    (hs : s ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (hqs0 : 0 ≤ logRatio X s - 1) (hqs5 : logRatio X s - 1 ≤ 5)
    (hqt5 : logRatio X t - 1 ≤ 5) :
    |dickmanContinuousWeight X s - dickmanContinuousWeight X t| ≤
      (X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2) * |s - t| := by
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hA_t := invMulLog_bound hk ht.1
  have hAdiff := invMulLog_cell_lipschitz hk hs ht
  have hQdiff := logRatio_cell_lipschitz X hX hk hs ht
  have hRdiff := (rho_logRatio_lipschitz X s t hqs5 hqt5).trans hQdiff
  have hRspos : 0 ≤ rho (logRatio X s - 1) :=
    (rho_pos_on_zero_five hqs0 hqs5).le
  have hRsle : rho (logRatio X s - 1) ≤ 1 :=
    rho_le_one_of_le_five hqs5
  have hAstabs : |invMulLog t| ≤ 2 / (k : ℝ) := by
    rw [abs_of_nonneg hA_t.1]
    exact hA_t.2
  have hrewrite (u : ℝ) :
      dickmanContinuousWeight X u =
        X * invMulLog u * rho (logRatio X u - 1) := by
    unfold dickmanContinuousWeight invMulLog logRatio
    ring
  rw [hrewrite, hrewrite]
  have halgebra :
      invMulLog s * rho (logRatio X s - 1) -
          invMulLog t * rho (logRatio X t - 1) =
        (invMulLog s - invMulLog t) * rho (logRatio X s - 1) +
          invMulLog t * (rho (logRatio X s - 1) -
            rho (logRatio X t - 1)) := by ring
  have hfactor :
      X * invMulLog s * rho (logRatio X s - 1) -
          X * invMulLog t * rho (logRatio X t - 1) =
        X * (invMulLog s * rho (logRatio X s - 1) -
          invMulLog t * rho (logRatio X t - 1)) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg hX0, halgebra]
  calc
    X * |(invMulLog s - invMulLog t) * rho (logRatio X s - 1) +
        invMulLog t * (rho (logRatio X s - 1) -
          rho (logRatio X t - 1))| ≤
      X * (|invMulLog s - invMulLog t| *
          |rho (logRatio X s - 1)| +
        |invMulLog t| * |rho (logRatio X s - 1) -
          rho (logRatio X t - 1)|) := by
      apply mul_le_mul_of_nonneg_left _ hX0
      simpa only [abs_mul] using abs_add_le
        ((invMulLog s - invMulLog t) * rho (logRatio X s - 1))
        (invMulLog t * (rho (logRatio X s - 1) -
          rho (logRatio X t - 1)))
    _ ≤ X * ((6 / (k : ℝ) ^ 2 * |s - t|) * 1 +
        (2 / (k : ℝ)) * ((4 * Real.log X / (k : ℝ)) * |s - t|)) := by
      have hRsabs : |rho (logRatio X s - 1)| ≤ 1 := by
        rw [abs_of_nonneg hRspos]
        exact hRsle
      have hBnonneg : 0 ≤ 6 / (k : ℝ) ^ 2 * |s - t| := by positivity
      have hCnonneg : 0 ≤ 2 / (k : ℝ) := by positivity
      have hterm1 :
          |invMulLog s - invMulLog t| * |rho (logRatio X s - 1)| ≤
            (6 / (k : ℝ) ^ 2 * |s - t|) * 1 :=
        mul_le_mul hAdiff hRsabs (abs_nonneg _) hBnonneg
      have hterm2 :
          |invMulLog t| * |rho (logRatio X s - 1) -
              rho (logRatio X t - 1)| ≤
            (2 / (k : ℝ)) *
              ((4 * Real.log X / (k : ℝ)) * |s - t|) :=
        mul_le_mul hAstabs hRdiff (abs_nonneg _) hCnonneg
      exact mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) hX0
    _ = (X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2) * |s - t| := by
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      field_simp
      ring

theorem dickmanContinuousWeight_cell_oscillation (X : ℝ) (hX : 1 ≤ X)
    {k : ℕ} (hk : 2 ≤ k) {t : ℝ}
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (hq : ∀ u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ),
      0 ≤ logRatio X u - 1 ∧ logRatio X u - 1 ≤ 5) :
    |dickmanContinuousWeight X (k + 1 : ℕ) -
        dickmanContinuousWeight X t| ≤
      X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2 := by
  have hs : ((k + 1 : ℕ) : ℝ) ∈
      Set.Icc (k : ℝ) (k + 1 : ℕ) := by constructor <;> norm_num
  have h := dickmanContinuousWeight_cell_lipschitz X hX hk hs ht
    (hq _ hs).1 (hq _ hs).2 (hq _ ht).2
  have hdist : |((k + 1 : ℕ) : ℝ) - t| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [ht.2])]
    norm_num
    linarith [ht.1]
  have hcoef : 0 ≤ X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2 := by
    have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
    positivity
  calc
    |dickmanContinuousWeight X (k + 1 : ℕ) -
        dickmanContinuousWeight X t| ≤
      (X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2) *
        |((k + 1 : ℕ) : ℝ) - t| := h
    _ ≤ (X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2) * 1 := by
      exact mul_le_mul_of_nonneg_left hdist hcoef
    _ = _ := by ring



theorem dickmanWeight_sum_integral_bound (X : ℕ) (hX : 1 ≤ X)
    {z y : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y)
    (hq : ∀ t ∈ Set.Icc (z : ℝ) (y : ℝ),
      1 ≤ logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6) :
    |(∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) -
        ∫ t in (z : ℝ)..(y : ℝ), dickmanContinuousWeight X t| ≤
      2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hXR
  have hcoef : 0 ≤ (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) := by positivity
  have hint : ∀ k ∈ Set.Ico z y,
      IntervalIntegrable (dickmanContinuousWeight (X : ℝ))
        MeasureTheory.volume (k : ℝ) (k + 1 : ℕ) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hz.trans hk.1
    have hcont : ContinuousOn (dickmanContinuousWeight (X : ℝ))
        (Set.Icc (k : ℝ) (k + 1 : ℕ)) :=
      (continuousOn_dickmanContinuousWeight (X : ℝ)).mono (fun t ht => by
        rw [Set.mem_Ioi]
        linarith [hk2, ht.1])
    rw [← Set.uIcc_of_le (by norm_num : (k : ℝ) ≤ (k + 1 : ℕ))] at hcont
    exact hcont.intervalIntegrable
  have hosc : ∀ k ∈ Finset.Ico z y,
      ∀ t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ),
        |dickmanContinuousWeight (X : ℝ) (k + 1 : ℕ) -
          dickmanContinuousWeight (X : ℝ) t| ≤
          (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (k : ℝ) ^ 2 := by
    intro k hk t ht
    rw [Finset.mem_Ico] at hk
    have hk2 : 2 ≤ k := hz.trans hk.1
    apply dickmanContinuousWeight_cell_oscillation (X : ℝ) hXR hk2 ht
    intro u hu
    have huglobal : u ∈ Set.Icc (z : ℝ) (y : ℝ) := by
      constructor
      · have hzk : (z : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
        exact hzk.trans hu.1
      · have hky : k + 1 ≤ y := by omega
        exact hu.2.trans (by exact_mod_cast hky)
    have huq := hq u huglobal
    exact ⟨by linarith [huq.1], by linarith [huq.2]⟩
  have hR := sum_integral_error_bound
    (dickmanContinuousWeight (X : ℝ))
    (fun k => (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (k : ℝ) ^ 2)
    hzy hint (by
      simpa only [Nat.cast_add, Nat.cast_one] using hosc)
  simp only [dickmanContinuousWeight_nat] at hR
  calc
    |(∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) -
        ∫ t in (z : ℝ)..(y : ℝ), dickmanContinuousWeight X t| ≤
      ∑ k ∈ Finset.Ico z y,
        (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (k : ℝ) ^ 2 := hR
    _ = ((X : ℝ) * (6 + 8 * Real.log (X : ℝ))) *
        ∑ k ∈ Finset.Ico z y, 1 / (k : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ ((X : ℝ) * (6 + 8 * Real.log (X : ℝ))) *
        (2 / (z : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ico_inv_sq_le (show 1 ≤ z by omega)) hcoef
    _ = 2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ) := by ring


/-! ## Quantitative PNT transfer for the Dickman prime weight

The following estimates combine the preceding Chebyshev--Stieltjes identity,
the audited medium PNT, and the explicit Dickman-weight oscillation bound.
They are the one-prime analytic input for the finite de Bruijn induction.
-/


















/-! ## Uniform floor stability for the recursive Dickman kernel -/

/-- Replacing a positive real quotient by its integer floor perturbs the
Dickman main term by an absolute constant, uniformly on the compact range
used by the four-mark induction. -/
theorem rho_floor_kernel_stability (A : ℕ) {r p : ℝ}
    (hA : 1 ≤ A) (hAr : (A : ℝ) ≤ r) (hrA : r < (A : ℝ) + 1)
    (hp : (2 : ℝ) ≤ p) (hb4 : Real.log r / Real.log p ≤ 4) :
    |(A : ℝ) * rho (Real.log (A : ℝ) / Real.log p) -
        r * rho (Real.log r / Real.log p)| ≤ 3 := by
  let a : ℝ := Real.log (A : ℝ) / Real.log p
  let b : ℝ := Real.log r / Real.log p
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hrpos : 0 < r := hApos.trans_le hAr
  have hppos : 0 < p := by linarith
  have hlogppos : 0 < Real.log p := Real.log_pos (by linarith)
  have hlogp_half : (1 / 2 : ℝ) ≤ Real.log p := by
    have hmono : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp
    nlinarith [Real.log_two_gt_d9]
  have hlogAr : Real.log (A : ℝ) ≤ Real.log r :=
    Real.log_le_log hApos hAr
  have hab : a ≤ b := by
    dsimp [a, b]
    exact div_le_div_of_nonneg_right hlogAr hlogppos.le
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hA)) hlogppos.le
  have hb0 : 0 ≤ b := ha0.trans hab
  have hb5 : b ≤ 5 := by dsimp [b]; linarith
  have hrhoa0 : 0 ≤ rho a :=
    (rho_pos_on_zero_five ha0 (hab.trans hb5)).le
  have hrhob0 : 0 ≤ rho b := (rho_pos_on_zero_five hb0 hb5).le
  have hrhob1 : rho b ≤ 1 := rho_le_one_of_le_five hb5
  have hrho : |rho a - rho b| ≤ b - a := by
    rw [abs_sub_comm]
    exact rho_lipschitz_of_le_five hab hb5
  have hlogquot : Real.log r - Real.log (A : ℝ) ≤
      r / (A : ℝ) - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hrpos hApos)
    rw [Real.log_div hrpos.ne' hApos.ne'] at h
    exact h
  have hscaled : (A : ℝ) *
      (Real.log r - Real.log (A : ℝ)) ≤ r - (A : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlogquot hApos.le
    calc
      (A : ℝ) * (Real.log r - Real.log (A : ℝ)) ≤
          (A : ℝ) * (r / (A : ℝ) - 1) := h
      _ = r - (A : ℝ) := by field_simp
  have hAdiff : (A : ℝ) * (b - a) ≤ 2 := by
    have hdiv := div_le_div_of_nonneg_right hscaled hlogppos.le
    have hfirst : (A : ℝ) * (b - a) ≤
        (r - (A : ℝ)) / Real.log p := by
      dsimp [a, b]
      convert hdiv using 1; ring
    have hsecond : (r - (A : ℝ)) / Real.log p ≤ 2 := by
      apply (div_le_iff₀ hlogppos).2
      nlinarith
    exact hfirst.trans hsecond
  have hgap0 : 0 ≤ r - (A : ℝ) := sub_nonneg.mpr hAr
  have hgap1 : r - (A : ℝ) ≤ 1 := by linarith
  calc
    _ = |(A : ℝ) * (rho a - rho b) +
          ((A : ℝ) - r) * rho b| := by dsimp [a, b]; congr 1; ring
    _ ≤ |(A : ℝ) * (rho a - rho b)| +
          |((A : ℝ) - r) * rho b| := abs_add_le _ _
    _ = (A : ℝ) * |rho a - rho b| +
          (r - (A : ℝ)) * rho b := by
      rw [abs_mul, abs_mul, abs_of_nonneg hApos.le,
        abs_of_nonpos (sub_nonpos.mpr hAr), abs_of_nonneg hrhob0]
      ring
    _ ≤ (A : ℝ) * (b - a) +
          (r - (A : ℝ)) * 1 := by gcongr
    _ ≤ 2 + 1 := add_le_add hAdiff (by simpa using hgap1)
    _ = 3 := by norm_num

/-- The integer quotient in the exact largest-prime recurrence and its real
Dickman model differ by at most three. -/
theorem dickmanPrimeSummand_floor_stability (X p : ℕ)
    (hp2 : 2 ≤ p) (hpX : p ≤ X)
    (hq5 : Real.log (X : ℝ) / Real.log (p : ℝ) ≤ 5) :
    |((X / p : ℕ) : ℝ) * rho (dickmanU (X / p) p) -
        dickmanPrimeSummand X p| ≤ 3 := by
  have hp0 : 0 < p := by omega
  have hX0 : 0 < X := hp0.trans_le hpX
  have hA : 1 ≤ X / p := by
    apply (Nat.le_div_iff_mul_le hp0).2
    simpa using hpX
  have hAr : ((X / p : ℕ) : ℝ) ≤ (X : ℝ) / (p : ℝ) :=
    Nat.cast_div_le
  have hupperNat : X < (X / p + 1) * p :=
    (Nat.div_lt_iff_lt_mul hp0).mp (Nat.lt_succ_self (X / p))
  have hrA : (X : ℝ) / (p : ℝ) < ((X / p : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ (by exact_mod_cast hp0 : (0 : ℝ) < p)).2
    exact_mod_cast hupperNat
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hlogdiv :
      Real.log ((X : ℝ) / (p : ℝ)) =
        Real.log (X : ℝ) - Real.log (p : ℝ) := by
    rw [Real.log_div (by exact_mod_cast hX0.ne' : (X : ℝ) ≠ 0)
      (by exact_mod_cast hp0.ne' : (p : ℝ) ≠ 0)]
  have hb4 : Real.log ((X : ℝ) / (p : ℝ)) /
      Real.log (p : ℝ) ≤ 4 := by
    rw [hlogdiv]
    apply (div_le_iff₀ hlogp).2
    have hq := (div_le_iff₀ hlogp).mp hq5
    linarith
  have hcoord : Real.log ((X : ℝ) / (p : ℝ)) /
      Real.log (p : ℝ) =
        Real.log (X : ℝ) / Real.log (p : ℝ) - 1 := by
    rw [hlogdiv]
    field_simp
  have hstab := rho_floor_kernel_stability (X / p) hA hAr hrA
    (by exact_mod_cast hp2) hb4
  rw [hcoord] at hstab
  simpa only [dickmanU, dickmanPrimeSummand] using hstab



































/-- The Dickman integral remains valid when the upper endpoint lies on the
birth face `u = 1`; differentiability is only needed in the open interval. -/
theorem integral_dickmanContinuousWeight_closed_top (X z y : ℝ)
    (hz : 1 < z) (hzy : z < y)
    (hq : ∀ t ∈ Set.Icc z y,
      1 ≤ Real.log X / Real.log t ∧
        Real.log X / Real.log t ≤ 6) :
    (∫ t in z..y, dickmanContinuousWeight X t) =
      dickmanAntiderivative X y - dickmanAntiderivative X z := by
  have hcontW : ContinuousOn
      (dickmanContinuousWeight X) (Set.Icc z y) :=
    (continuousOn_dickmanContinuousWeight X).mono (fun t ht => by
      rw [Set.mem_Ioi]
      exact hz.trans_le ht.1)
  have hint : IntervalIntegrable (dickmanContinuousWeight X)
      MeasureTheory.volume z y := by
    rw [← Set.uIcc_of_le hzy.le] at hcontW
    exact hcontW.intervalIntegrable
  have hcontA : ContinuousOn
      (dickmanAntiderivative X) (Set.Icc z y) := by
    intro t ht
    have ht1 : 1 < t := hz.trans_le ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlogne : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    have hqcont : ContinuousAt (fun s : ℝ => Real.log X / Real.log s) t :=
      continuousAt_const.div (Real.continuousAt_log ht0) hlogne
    exact (continuousAt_const.mul
      (continuous_rho.continuousAt.comp hqcont)).continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hzy.le hcontA
  · intro t ht
    have htI : t ∈ Set.Icc z y := ⟨ht.1.le, ht.2.le⟩
    have hqt6 := (hq t htI).2
    have hlogt : 0 < Real.log t := Real.log_pos (hz.trans ht.1)
    have hlogy : 0 < Real.log y := Real.log_pos (hz.trans hzy)
    have hlogty : Real.log t < Real.log y :=
      Real.strictMonoOn_log (show t ∈ Set.Ioi 0 by
        exact hz.trans ht.1 |>.trans' (by norm_num))
        (show y ∈ Set.Ioi 0 by exact hz.trans hzy |>.trans' (by norm_num)) ht.2
    have hqy1 := (hq y ⟨hzy.le, le_rfl⟩).1
    have hlogX : 0 < Real.log X := by
      have h := (le_div_iff₀ hlogy).mp hqy1
      linarith
    have hqstrict : 1 < Real.log X / Real.log t := by
      have hdiv : Real.log X / Real.log y < Real.log X / Real.log t := by
        exact (div_lt_div_iff_of_pos_left hlogX hlogy hlogt).2 hlogty
      exact hqy1.trans_lt hdiv
    exact hasDerivAt_dickmanAntiderivative X t (hz.trans ht.1)
      hqstrict hqt6
  · exact hint

/-- Prime-sum approximation with the upper endpoint allowed on `u = 1`. -/
theorem dickmanPrimeSum_pnt_bound_closed_top (X : ℕ) (hX : 1 ≤ X)
    {C : ℝ} (hC : 0 ≤ C) {X₀ z y : ℕ}
    (hbound : ∀ T, X₀ ≤ T →
      |primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / (Real.log (T : ℝ)) ^ (3 : ℝ)))
    (hX₀z : X₀ ≤ z) (hz : 2 ≤ z) (hzy : z < y)
    (hq : ∀ t ∈ Set.Icc (z : ℝ) (y : ℝ),
      1 ≤ logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6) :
    |(∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
        dickmanPrimeSummand X p) -
      (dickmanAntiderivative (X : ℝ) (y : ℝ) -
        dickmanAntiderivative (X : ℝ) (z : ℝ))| ≤
      500 * C * (X : ℝ) / Real.log (z : ℝ) +
        2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ) := by
  have hpnt := dickmanWeight_pnt_bound X hX hC hbound hX₀z hz hzy hq
  rw [primeThetaWeightedInterval_dickman,
    integerAbelMain_eq_sum_Ioc (dickmanThetaWeight X) hzy] at hpnt
  have hriemann := dickmanWeight_sum_integral_bound X hX hz hzy.le hq
  have hintegral := integral_dickmanContinuousWeight_closed_top
    (X : ℝ) (z : ℝ) (y : ℝ)
    (by exact_mod_cast (show 1 < z by omega))
    (by exact_mod_cast hzy) hq
  rw [hintegral] at hriemann
  calc
    _ = |((∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
          dickmanPrimeSummand X p) -
          ∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) +
        ((∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) -
          (dickmanAntiderivative (X : ℝ) (y : ℝ) -
            dickmanAntiderivative (X : ℝ) (z : ℝ)))| := by ring_nf
    _ ≤ |(∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
          dickmanPrimeSummand X p) -
          ∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m| +
        |(∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) -
          (dickmanAntiderivative (X : ℝ) (y : ℝ) -
            dickmanAntiderivative (X : ℝ) (z : ℝ))| := abs_add_le _ _
    _ ≤ _ := add_le_add hpnt hriemann

/-- Reverse (complement) method-of-steps inequality.  It starts from an upper
cutoff and solves the exact recursion for the lower cutoff. -/
theorem friableCount_reverse_step_pnt_bound (X : ℕ) (hX : 1 ≤ X)
    {C E₁ : ℝ} (hC : 0 ≤ C) {X₀ z y : ℕ}
    (hbound : ∀ T, X₀ ≤ T →
      |primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / (Real.log (T : ℝ)) ^ (3 : ℝ)))
    (hX₀z : X₀ ≤ z) (hz : 2 ≤ z) (hzy : z < y)
    (hq : ∀ t ∈ Set.Icc (z : ℝ) (y : ℝ),
      1 ≤ logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6)
    (e : ℕ → ℝ)
    (htop : |(friableCount X y : ℝ) -
        dickmanAntiderivative (X : ℝ) (y : ℝ)| ≤ E₁)
    (hquot : ∀ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
      |(friableCount (X / p) p : ℝ) - dickmanPrimeSummand X p| ≤ e p) :
    |(friableCount X z : ℝ) -
        dickmanAntiderivative (X : ℝ) (z : ℝ)| ≤
      E₁ + (∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow, e p) +
        (500 * C * (X : ℝ) / Real.log (z : ℝ) +
          2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ)) := by
  let P := (y + 1).primesBelow \ (z + 1).primesBelow
  have hrecNat := friableCount_prime_interval X (Nat.succ_le_iff.mp hX) hzy.le
  have hrec : (friableCount X y : ℝ) = (friableCount X z : ℝ) +
      ∑ p ∈ P, (friableCount (X / p) p : ℝ) := by
    exact_mod_cast hrecNat
  have hsum :
      |(∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
          ∑ p ∈ P, dickmanPrimeSummand X p| ≤
        ∑ p ∈ P, e p := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ P,
          |(friableCount (X / p) p : ℝ) - dickmanPrimeSummand X p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ P, e p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hquot p (by simpa [P] using hp)
  have hprime := dickmanPrimeSum_pnt_bound_closed_top
    X hX hC hbound hX₀z hz hzy hq
  change |(∑ p ∈ P, dickmanPrimeSummand X p) -
      (dickmanAntiderivative (X : ℝ) (y : ℝ) -
        dickmanAntiderivative (X : ℝ) (z : ℝ))| ≤ _ at hprime
  have hrearrange : (friableCount X z : ℝ) =
      (friableCount X y : ℝ) -
        ∑ p ∈ P, (friableCount (X / p) p : ℝ) := by linarith
  rw [hrearrange]
  calc
    _ = |((friableCount X y : ℝ) -
          dickmanAntiderivative (X : ℝ) (y : ℝ)) -
        ((∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
          ∑ p ∈ P, dickmanPrimeSummand X p) -
        ((∑ p ∈ P, dickmanPrimeSummand X p) -
          (dickmanAntiderivative (X : ℝ) (y : ℝ) -
            dickmanAntiderivative (X : ℝ) (z : ℝ)))| := by ring_nf
    _ ≤ |(friableCount X y : ℝ) -
          dickmanAntiderivative (X : ℝ) (y : ℝ)| +
        (|(∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
            ∑ p ∈ P, dickmanPrimeSummand X p| +
          |(∑ p ∈ P, dickmanPrimeSummand X p) -
            (dickmanAntiderivative (X : ℝ) (y : ℝ) -
              dickmanAntiderivative (X : ℝ) (z : ℝ))|) := by
      calc
        _ = |((friableCount X y : ℝ) -
              dickmanAntiderivative (X : ℝ) (y : ℝ)) +
            (-((∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
              ∑ p ∈ P, dickmanPrimeSummand X p) +
            -((∑ p ∈ P, dickmanPrimeSummand X p) -
              (dickmanAntiderivative (X : ℝ) (y : ℝ) -
                dickmanAntiderivative (X : ℝ) (z : ℝ))))| := by ring_nf
        _ ≤ |(friableCount X y : ℝ) -
              dickmanAntiderivative (X : ℝ) (y : ℝ)| +
            |-((∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
                ∑ p ∈ P, dickmanPrimeSummand X p) +
              -((∑ p ∈ P, dickmanPrimeSummand X p) -
                (dickmanAntiderivative (X : ℝ) (y : ℝ) -
                  dickmanAntiderivative (X : ℝ) (z : ℝ)))| := abs_add_le _ _
        _ ≤ |(friableCount X y : ℝ) -
              dickmanAntiderivative (X : ℝ) (y : ℝ)| +
            (|-((∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
                ∑ p ∈ P, dickmanPrimeSummand X p)| +
              |-((∑ p ∈ P, dickmanPrimeSummand X p) -
                (dickmanAntiderivative (X : ℝ) (y : ℝ) -
                  dickmanAntiderivative (X : ℝ) (z : ℝ)))|) :=
          add_le_add le_rfl (abs_add_le _ _)
        _ = _ := by simp only [abs_neg]
    _ ≤ E₁ + ((∑ p ∈ P, e p) +
        (500 * C * (X : ℝ) / Real.log (z : ℝ) +
          2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ))) := by
      exact add_le_add htop (add_le_add hsum hprime)
    _ = _ := by
      dsimp [P]
      ring

theorem friableCount_top_exact {X : ℕ} (hX : 2 ≤ X) :
    (friableCount X X : ℝ) = dickmanAntiderivative (X : ℝ) (X : ℝ) := by
  have hlog : Real.log (X : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by positivity)
      (by exact_mod_cast (show X ≠ 1 by omega))
  rw [friableCount_eq_self le_rfl, dickmanAntiderivative,
    div_self hlog, rho_one]
  ring

/-- The number of primes in `(z,Y]` has the elementary Chebyshev bound at
the exact scale needed to sum the uniform floor error. -/
theorem primeInterval_card_le (z Y : ℕ) (hz : 2 ≤ z) :
    (((Y + 1).primesBelow \ (z + 1).primesBelow).card : ℝ) ≤
      Real.log 4 * (Y : ℝ) / Real.log (z : ℝ) := by
  let P := (Y + 1).primesBelow \ (z + 1).primesBelow
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlower : (P.card : ℝ) * Real.log (z : ℝ) ≤
      ∑ p ∈ P, Real.log (p : ℝ) := by
    calc
      _ = ∑ p ∈ P, Real.log (z : ℝ) := by simp [Finset.sum_const]
      _ ≤ ∑ p ∈ P, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpout := (Finset.mem_sdiff.mp hp).2
        have hpz : z < p := by
          by_contra hnot
          apply hpout
          rw [Nat.mem_primesBelow]
          exact ⟨by omega,
            Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1⟩
        exact Real.log_le_log (by positivity) (by exact_mod_cast hpz.le)
  have hupper : (∑ p ∈ P, Real.log (p : ℝ)) ≤
      Real.log 4 * (Y : ℝ) := by
    calc
      _ ≤ ∑ p ∈ (Y + 1).primesBelow, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        intro p hp hnot
        have hpprime := Nat.prime_of_mem_primesBelow hp
        exact Real.log_nonneg (by exact_mod_cast hpprime.one_le)
      _ = primeLogSumUpTo Y := rfl
      _ = Chebyshev.theta (Y : ℝ) := primeLogSumUpTo_eq_theta Y
      _ ≤ Real.log 4 * (Y : ℝ) :=
        Chebyshev.theta_le_log4_mul_x (by positivity)
  apply (le_div_iff₀ hlogz).2
  exact hlower.trans hupper

/-- The endpoint Riemann error is eventually at most one copy of the natural
`X / log y` error scale, uniformly for `X ≤ y^5`. -/
theorem exists_dickmanRiemann_remainder_threshold :
    ∃ Y₀ : ℕ, ∀ {y X : ℕ}, Y₀ ≤ y → 2 ≤ y → 1 ≤ X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ) ≤
        (X : ℝ) / Real.log (y : ℝ) := by
  have hlogdivReal : Filter.Tendsto
      (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogdiv : Filter.Tendsto
      (fun y : ℕ => Real.log (y : ℝ) / (y : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, id_eq] using
      hlogdivReal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlogsqdivReal : Filter.Tendsto
      (fun x : ℝ => Real.log x ^ (2 : ℝ) / x ^ (1 : ℝ))
      Filter.atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hlogsqdiv : Filter.Tendsto
      (fun y : ℕ => Real.log (y : ℝ) ^ 2 / (y : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [Real.rpow_natCast, Real.rpow_one] using
      hlogsqdivReal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have htotal : Filter.Tendsto
      (fun y : ℕ =>
        12 * (Real.log (y : ℝ) / (y : ℝ)) +
          80 * (Real.log (y : ℝ) ^ 2 / (y : ℝ)))
      Filter.atTop (nhds 0) := by
    have h12 : Filter.Tendsto (fun _ : ℕ => (12 : ℝ))
        Filter.atTop (nhds 12) := tendsto_const_nhds
    have h80 : Filter.Tendsto (fun _ : ℕ => (80 : ℝ))
        Filter.atTop (nhds 80) := tendsto_const_nhds
    convert (h12.mul hlogdiv).add (h80.mul hlogsqdiv) using 1
    norm_num
  have hevent : ∀ᶠ y : ℕ in Filter.atTop,
      12 * (Real.log (y : ℝ) / (y : ℝ)) +
          80 * (Real.log (y : ℝ) ^ 2 / (y : ℝ)) ≤ 1 := by
    have hlt := htotal.eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hlt] with y hy
    exact hy.le
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨Y₀, ?_⟩
  intro y X hY₀y hy2 hX hlogX
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hypos : (0 : ℝ) < (y : ℝ) := by positivity
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hscaled :
      2 * (6 + 8 * Real.log (X : ℝ)) * Real.log (y : ℝ) /
          (y : ℝ) ≤ 1 := by
    have hinside : 6 + 8 * Real.log (X : ℝ) ≤
        6 + 40 * Real.log (y : ℝ) := by linarith
    calc
      _ = (2 * Real.log (y : ℝ) / (y : ℝ)) *
          (6 + 8 * Real.log (X : ℝ)) := by ring
      _ ≤ (2 * Real.log (y : ℝ) / (y : ℝ)) *
          (6 + 40 * Real.log (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hinside (by positivity)
      _ = 2 * (6 + 40 * Real.log (y : ℝ)) * Real.log (y : ℝ) /
          (y : ℝ) := by ring
      _ = 12 * (Real.log (y : ℝ) / (y : ℝ)) +
          80 * (Real.log (y : ℝ) ^ 2 / (y : ℝ)) := by ring
      _ ≤ 1 := hY₀ y hY₀y
  apply (le_div_iff₀ hlogy).2
  calc
    (2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ)) *
        Real.log (y : ℝ) =
      (X : ℝ) *
        (2 * (6 + 8 * Real.log (X : ℝ)) * Real.log (y : ℝ) /
          (y : ℝ)) := by ring
    _ ≤ (X : ℝ) * 1 := mul_le_mul_of_nonneg_left hscaled hXpos.le
    _ = (X : ℝ) := by ring

/-- Uniform finite de Bruijn estimate on the full four-mark coordinate
range.  This is a closed theorem: the PNT, contraction, and endpoint
thresholds are all chosen internally. -/
theorem exists_uniform_friableCount_dickman_bound :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → y ≤ X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |(friableCount X y : ℝ) - (X : ℝ) * rho (dickmanU X y)| ≤
        K * (X : ℝ) / Real.log (y : ℝ) := by
  obtain ⟨C, hCpos, X₀, hbound⟩ :=
    exists_primeLogSumUpTo_error_bound (3 : ℝ)
  obtain ⟨Zc, hcontract⟩ := exists_primeInvLogSum_contraction_threshold
  obtain ⟨Zr, hriemann⟩ := exists_dickmanRiemann_remainder_threshold
  let K : ℝ := 10 * (500 * C + 3 * Real.log 4 + 1)
  let Y₀ : ℕ := max 2 (max X₀ (max Zc Zr))
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, Y₀, ?_⟩
  intro X
  induction X using Nat.strong_induction_on with
  | h X ih =>
      intro y hY₀y hyX hlogXy
      have hy2 : 2 ≤ y := (le_max_left 2 (max X₀ (max Zc Zr))).trans hY₀y
      have hypos : 0 < y := by omega
      have hX2 : 2 ≤ X := hy2.trans hyX
      have hXpos : 0 < X := by omega
      have hlogy : 0 < Real.log (y : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < y by omega))
      by_cases hyXeq : y = X
      · subst y
        rw [friableCount_top_exact hX2]
        simp only [dickmanAntiderivative, dickmanU, sub_self, abs_zero]
        positivity
      · have hyXlt : y < X := lt_of_le_of_ne hyX hyXeq
        let P := (X + 1).primesBelow \ (y + 1).primesBelow
        let e : ℕ → ℝ := fun p =>
          K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ) + 3
        have hX₀y : X₀ ≤ y :=
          (le_max_left X₀ (max Zc Zr)).trans
            ((le_max_right 2 (max X₀ (max Zc Zr))).trans hY₀y)
        have hZcy : Zc ≤ y :=
          (le_max_left Zc Zr).trans
            ((le_max_right X₀ (max Zc Zr)).trans
              ((le_max_right 2 (max X₀ (max Zc Zr))).trans hY₀y))
        have hZry : Zr ≤ y :=
          (le_max_right Zc Zr).trans
            ((le_max_right X₀ (max Zc Zr)).trans
              ((le_max_right 2 (max X₀ (max Zc Zr))).trans hY₀y))
        have hq : ∀ t ∈ Set.Icc (y : ℝ) (X : ℝ),
            1 ≤ logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6 := by
          intro t ht
          have ht1 : 1 < t :=
            (by exact_mod_cast (show 1 < y by omega) : (1 : ℝ) < y).trans_le ht.1
          have hlogt : 0 < Real.log t := Real.log_pos ht1
          have hlogtX : Real.log t ≤ Real.log (X : ℝ) := by
            apply Real.log_le_log (by linarith)
            exact ht.2
          have hlogyt : Real.log (y : ℝ) ≤ Real.log t := by
            apply Real.log_le_log (by positivity)
            exact ht.1
          constructor
          · dsimp [logRatio]
            apply (le_div_iff₀ hlogt).2
            simpa using hlogtX
          · dsimp [logRatio]
            apply (div_le_iff₀ hlogt).2
            linarith
        have hquot : ∀ p ∈ P,
            |(friableCount (X / p) p : ℝ) - dickmanPrimeSummand X p| ≤ e p := by
          intro p hpP
          have hpfull : p ∈ (X + 1).primesBelow \ (y + 1).primesBelow := by
            simpa [P] using hpP
          have hpprime : p.Prime :=
            Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hpfull).1
          have hpX : p ≤ X := by
            have := (Nat.lt_of_mem_primesBelow
              (Finset.mem_sdiff.mp hpfull).1)
            omega
          have hyp : y < p := by
            have hpout := (Finset.mem_sdiff.mp hpfull).2
            by_contra hnot
            apply hpout
            rw [Nat.mem_primesBelow]
            exact ⟨by omega, hpprime⟩
          have hp2 : 2 ≤ p := hpprime.two_le
          have hlogp : 0 < Real.log (p : ℝ) :=
            Real.log_pos (by exact_mod_cast hpprime.one_lt)
          have hlogyp : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hyp.le)
          have hq5 : Real.log (X : ℝ) / Real.log (p : ℝ) ≤ 5 := by
            apply (div_le_iff₀ hlogp).2
            linarith
          have hfloor := dickmanPrimeSummand_floor_stability X p hp2 hpX hq5
          have hApos : 1 ≤ X / p :=
            (Nat.le_div_iff_mul_le hpprime.pos).2 (by simpa using hpX)
          have hcount :
              |(friableCount (X / p) p : ℝ) -
                ((X / p : ℕ) : ℝ) * rho (dickmanU (X / p) p)| ≤
                K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ) := by
            by_cases hpA : p ≤ X / p
            · have hAX : X / p < X := Nat.div_lt_self hXpos hpprime.one_lt
              have hlogAX : Real.log ((X / p : ℕ) : ℝ) ≤
                  Real.log (X : ℝ) := by
                apply Real.log_le_log (by exact_mod_cast hApos)
                exact_mod_cast Nat.div_le_self X p
              have hlogA5 : Real.log ((X / p : ℕ) : ℝ) ≤
                  5 * Real.log (p : ℝ) := by
                have := (div_le_iff₀ hlogp).mp hq5
                exact hlogAX.trans this
              exact ih (X / p) hAX (y := p)
                (hY₀y.trans hyp.le) hpA hlogA5
            · have hAp : X / p ≤ p := le_of_not_ge hpA
              rw [friableCount_eq_dickman_initial hApos hpprime.one_lt hAp,
                sub_self, abs_zero]
              positivity
          calc
            _ ≤ |(friableCount (X / p) p : ℝ) -
                  ((X / p : ℕ) : ℝ) * rho (dickmanU (X / p) p)| +
                |((X / p : ℕ) : ℝ) * rho (dickmanU (X / p) p) -
                  dickmanPrimeSummand X p| := by
              exact abs_sub_le _ _ _
            _ ≤ K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ) + 3 :=
              add_le_add hcount hfloor
            _ = e p := rfl
        have htop : |(friableCount X X : ℝ) -
            dickmanAntiderivative (X : ℝ) (X : ℝ)| ≤ 0 := by
          rw [friableCount_top_exact hX2, sub_self, abs_zero]
        have hreverse := friableCount_reverse_step_pnt_bound
          X hXpos hCpos.le hbound hX₀y hy2 hyXlt hq e htop
          (fun p hp => hquot p (by simpa [P] using hp))
        have hsumA : (∑ p ∈ P,
              K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ)) ≤
            K * (X : ℝ) * primeInvLogSum y X := by
          rw [primeInvLogSum]
          calc
            _ ≤ ∑ p ∈ P,
                K * (X : ℝ) *
                  (1 / ((p : ℝ) * Real.log (p : ℝ))) := by
              apply Finset.sum_le_sum
              intro p hpP
              have hpfull : p ∈ (X + 1).primesBelow \ (y + 1).primesBelow := by
                simpa [P] using hpP
              have hpprime : p.Prime :=
                Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hpfull).1
              have hlogp : 0 < Real.log (p : ℝ) :=
                Real.log_pos (by exact_mod_cast hpprime.one_lt)
              have hcast : ((X / p : ℕ) : ℝ) ≤ (X : ℝ) / (p : ℝ) :=
                Nat.cast_div_le
              calc
                _ ≤ K * ((X : ℝ) / (p : ℝ)) / Real.log (p : ℝ) := by
                  gcongr
                _ = K * (X : ℝ) *
                    (1 / ((p : ℝ) * Real.log (p : ℝ))) := by field_simp
            _ = K * (X : ℝ) *
                (∑ p ∈ P, 1 / ((p : ℝ) * Real.log (p : ℝ))) := by
              rw [Finset.mul_sum]
            _ = _ := by congr 2
        have hcontractYX : primeInvLogSum y X ≤
            9 / (10 * Real.log (y : ℝ)) :=
          hcontract hZcy hyXlt hlogXy
        have hsumAcontract : (∑ p ∈ P,
              K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ)) ≤
            (9 / 10 * K) * (X : ℝ) / Real.log (y : ℝ) := by
          calc
            _ ≤ K * (X : ℝ) * primeInvLogSum y X := hsumA
            _ ≤ K * (X : ℝ) * (9 / (10 * Real.log (y : ℝ))) := by
              gcongr
            _ = (9 / 10 * K) * (X : ℝ) /
                Real.log (y : ℝ) := by ring
        have hcard := primeInterval_card_le y X hy2
        have hsume : (∑ p ∈ P, e p) ≤
            (9 / 10 * K + 3 * Real.log 4) * (X : ℝ) /
              Real.log (y : ℝ) := by
          calc
            _ = (∑ p ∈ P,
                K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ)) +
                3 * (P.card : ℝ) := by
              simp only [e, Finset.sum_add_distrib, Finset.sum_const,
                nsmul_eq_mul]
              ring
            _ ≤ (9 / 10 * K) * (X : ℝ) / Real.log (y : ℝ) +
                3 * (Real.log 4 * (X : ℝ) / Real.log (y : ℝ)) :=
              add_le_add hsumAcontract (mul_le_mul_of_nonneg_left
                (by simpa [P] using hcard) (by norm_num))
            _ = (9 / 10 * K + 3 * Real.log 4) * (X : ℝ) /
                Real.log (y : ℝ) := by ring
        have hR := hriemann hZry hy2 hXpos hlogXy
        have hreverse' :
            |(friableCount X y : ℝ) -
                dickmanAntiderivative (X : ℝ) (y : ℝ)| ≤
              (9 / 10 * K + 3 * Real.log 4 + 500 * C + 1) *
                (X : ℝ) / Real.log (y : ℝ) := by
          calc
            _ ≤ 0 + (∑ p ∈ P, e p) +
                (500 * C * (X : ℝ) / Real.log (y : ℝ) +
                  2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) /
                    (y : ℝ)) := by simpa [P] using hreverse
            _ ≤ (∑ p ∈ P, e p) +
                (500 * C * (X : ℝ) / Real.log (y : ℝ) +
                  (X : ℝ) / Real.log (y : ℝ)) := by
              simpa only [zero_add] using
                add_le_add le_rfl (add_le_add le_rfl hR)
            _ ≤ (9 / 10 * K + 3 * Real.log 4) * (X : ℝ) /
                  Real.log (y : ℝ) +
                (500 * C * (X : ℝ) / Real.log (y : ℝ) +
                  (X : ℝ) / Real.log (y : ℝ)) :=
              add_le_add hsume le_rfl
            _ = (9 / 10 * K + 3 * Real.log 4 + 500 * C + 1) *
                (X : ℝ) / Real.log (y : ℝ) := by ring
        have hcoeff : 9 / 10 * K + 3 * Real.log 4 + 500 * C + 1 = K := by
          dsimp [K]
          ring
        rw [hcoeff] at hreverse'
        simpa only [dickmanAntiderivative] using hreverse'









end Erdos390.Full.FriableAsymptotic

end

theorem solution :
∃ K,
  And (LT.lt.{0} (0 : Real) K)
    (∃ Y₀,
      ∀ {X y : Nat},
        LE.le.{0} Y₀ y →
          LE.le.{0} y X →
            LE.le.{0} (Real.log ↑X) (HMul.hMul.{0, 0, 0} (5 : Real) (Real.log ↑y)) →
              LE.le.{0}
                (abs.{0}
                  (HSub.hSub.{0, 0, 0} (↑(Erdos390.Full.FriableAsymptotic.friableCount X y))
                    (HMul.hMul.{0, 0, 0} (↑X)
                      (Erdos390.Full.DickmanBasic.rho (Erdos390.Full.FriableAsymptotic.dickmanU X y)))))
                (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} K ↑X) (Real.log ↑y))) := by
  exact @Erdos390.Full.FriableAsymptotic.exists_uniform_friableCount_dickman_bound
