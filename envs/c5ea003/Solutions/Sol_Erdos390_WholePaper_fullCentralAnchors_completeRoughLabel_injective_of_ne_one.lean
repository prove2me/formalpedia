-- Prove2me | solution 1 for Erdos390.WholePaper.fullCentralAnchors_completeRoughLabel_injective_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:07:39.270912+00:00
-- url     : https://prove2.me/submissions/79e26d76-8a88-4899-956a-5d5023652b19

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006

/- Source module: Erdos390.WholePaper.StationaryLayers -/
section


/-!
# Stationary prime layers

For a fixed row `r`, Section 3 uses the prime interval
`n / (r + 1) < p ≤ 2n / (2r + 1)`.  The definition below records the
endpoints by cross-multiplied natural-number inequalities, so there is no
rounding ambiguity.  Its cardinality is then identified with the exact
prime-counting difference to which the fixed-interval PNT applies.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section



@[simp]
theorem mem_stationaryPrimeLayer {n r p : ℕ} :
    p ∈ stationaryPrimeLayer n r ↔
      p.Prime ∧ n < p * (r + 1) ∧ p * (2 * r + 1) ≤ 2 * n := by
  simp only [stationaryPrimeLayer, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun hp ↦ hp.2
  · intro hp
    have hpLe : p ≤ 2 * n :=
      (Nat.le_mul_of_pos_right p (by omega : 0 < 2 * r + 1)).trans hp.2.2
    exact ⟨by omega, hp⟩

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralPromotion -/
section


/-! # Promotion of residual central prime powers

This file formalizes the elementary promotion step from Section 10 of the
paper.  A positive block `B ≤ 2n` is multiplied by the least power of two
which puts it above `n`; the resulting block still lies at most `2n`.
-/

namespace Erdos390.WholePaper

noncomputable section





theorem promotionExponent_spec {n B : ℕ} (hB : 0 < B) :
    n < 2 ^ promotionExponent n B * B := by
  have htarget : n / B + 1 ≤ 2 ^ promotionExponent n B := by
    simpa only [promotionExponent] using
      Nat.le_pow_clog Nat.one_lt_two (n / B + 1)
  apply (Nat.div_lt_iff_lt_mul hB).mp
  omega

theorem promotionExponent_minimal {n B k : ℕ}
    (hk : k < promotionExponent n B) :
    2 ^ k * B ≤ n := by
  have hpow : 2 ^ k < n / B + 1 := by
    exact (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mp hk
  have hpow' : 2 ^ k ≤ n / B := by omega
  exact (Nat.mul_le_mul_right B hpow').trans (Nat.div_mul_le_self n B)

theorem promotedBlock_gt {n B : ℕ} (hB : 0 < B) :
    n < promotedBlock n B := by
  exact promotionExponent_spec hB

theorem promotedBlock_le_two_mul {n B : ℕ}
    (hB : 0 < B) (hBupper : B ≤ 2 * n) :
    promotedBlock n B ≤ 2 * n := by
  by_cases hBn : B ≤ n
  · have hdivPos : 0 < n / B := Nat.div_pos hBn hB
    have htarget : 1 < n / B + 1 := by omega
    have hkPos : 0 < promotionExponent n B := by
      simpa only [promotionExponent] using
        Nat.clog_pos Nat.one_lt_two htarget
    have hkPred : promotionExponent n B - 1 < promotionExponent n B := by
      omega
    have hprevious : 2 ^ (promotionExponent n B - 1) * B ≤ n :=
      promotionExponent_minimal hkPred
    have hkSplit : promotionExponent n B - 1 + 1 = promotionExponent n B := by
      omega
    rw [promotedBlock, ← hkSplit, pow_succ]
    calc
      (2 ^ (promotionExponent n B - 1) * 2) * B =
          2 * (2 ^ (promotionExponent n B - 1) * B) := by ac_rfl
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 hprevious
  · have hnB : n < B := Nat.lt_of_not_ge hBn
    have hdiv : n / B = 0 := Nat.div_eq_of_lt hnB
    simp [promotedBlock, promotionExponent, hdiv, hBupper]

theorem promotedBlock_mem_centralInterval {n B : ℕ}
    (hB : 0 < B) (hBupper : B ≤ 2 * n) :
    promotedBlock n B ∈ Finset.Ioc n (2 * n) := by
  exact Finset.mem_Ioc.mpr
    ⟨promotedBlock_gt hB, promotedBlock_le_two_mul hB hBupper⟩





theorem centralPrimeBlock_pos (n p : ℕ) : 0 < centralPrimeBlock n p := by
  cases p with
  | zero => simp [centralPrimeBlock]
  | succ p =>
      simpa only [centralPrimeBlock] using
        (pow_pos (Nat.succ_pos p)
          ((Nat.choose (2 * n) n).factorization (p + 1)))

theorem centralPrimeBlock_le_two_mul {n p : ℕ} (hn : 0 < n) :
    centralPrimeBlock n p ≤ 2 * n := by
  simpa only [centralPrimeBlock] using
    (Nat.pow_factorization_choose_le
      (p := p) (n := 2 * n) (k := n) (by omega))







theorem promotedCentralFactor_mem_centralInterval {n p : ℕ} (hn : 0 < n) :
    promotedCentralFactor n p ∈ Finset.Ioc n (2 * n) := by
  exact promotedBlock_mem_centralInterval
    (centralPrimeBlock_pos n p) (centralPrimeBlock_le_two_mul hn)

theorem promotedCentralFactor_gt {n p : ℕ} (hn : 0 < n) :
    n < promotedCentralFactor n p :=
  (Finset.mem_Ioc.mp (promotedCentralFactor_mem_centralInterval hn)).1











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.ResidualCentralFactors -/
section


/-! # The finite family of promoted residual central factors -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section









theorem residualCentralPrimes_le {n X p : ℕ}
    (hp : p ∈ residualCentralPrimes n X) : p ≤ X :=
  (Finset.mem_filter.mp hp).2

theorem residualCentralPrimes_exponent_pos {n X p : ℕ}
    (hp : p ∈ residualCentralPrimes n X) :
    0 < (Nat.choose (2 * n) n).factorization p := by
  have hpMem : p ∈ (Nat.choose (2 * n) n).primeFactors :=
    (Finset.mem_filter.mp hp).1
  have hchoosePos : 0 < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  exact (Nat.prime_of_mem_primeFactors hpMem).factorization_pos_of_dvd
    hchoosePos.ne' (Nat.dvd_of_mem_primeFactors hpMem)









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralPrimeBlockDecomposition -/
section


/-!
# Exact low/high decomposition of the central binomial coefficient

The central binomial coefficient is the product of its complete prime-power
blocks.  Splitting those blocks at the anchor cutoff and promoting every low
block therefore introduces exactly one aggregate power of two and no other
valuation error.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



theorem largeCentralPrimes_prime {n X p : ℕ}
    (hp : p ∈ largeCentralPrimes n X) : p.Prime := by
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

theorem largeCentralPrimes_gt {n X p : ℕ}
    (hp : p ∈ largeCentralPrimes n X) : X < p :=
  (Finset.mem_filter.mp hp).2











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralCarryAnchors -/
section


/-! # Exact arithmetic of the fixed-prefix central carry anchors -/

namespace Erdos390.WholePaper

noncomputable section





/-- Every allowed allocation cofactor places its carry prime anchor in the
central interval. -/
theorem stationaryPrimeLayer_mul_cofactor_mem_centralInterval
    {n r p q : ℕ} (hp : p ∈ stationaryPrimeLayer n r)
    (hqLower : r + 1 ≤ q) (hqUpper : q ≤ 2 * r + 1) :
    p * q ∈ Finset.Ioc n (2 * n) := by
  have hmem := mem_stationaryPrimeLayer.mp hp
  apply Finset.mem_Ioc.mpr
  constructor
  · exact hmem.2.1.trans_le (Nat.mul_le_mul_left p hqLower)
  · exact (Nat.mul_le_mul_left p hqUpper).trans hmem.2.2



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorCollision -/
section


/-!
# Collision guards for the three central-anchor families

The prefix and row-zero anchors carry a marker prime above a fixed cutoff.
Every promoted residual factor is supported only at `2` and its base prime,
both below that cutoff.  The lemmas below turn this unique-factorization
observation into literal natural-number noncollision statements.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- A prime divisor of `A_p = 2^k p^e` is either `2` or the base prime
`p`. -/
theorem prime_dvd_promotedCentralFactor
    {n p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (hdiv : ℓ ∣ promotedCentralFactor n p) :
    ℓ = 2 ∨ ℓ = p := by
  rw [promotedCentralFactor, promotedBlock, centralPrimeBlock] at hdiv
  rcases hℓ.dvd_mul.mp hdiv with htwo | hpPow
  · left
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp
      (hℓ.dvd_of_dvd_pow htwo)
  · right
    exact (Nat.prime_dvd_prime_iff_eq hℓ hp).mp
      (hℓ.dvd_of_dvd_pow hpPow)

/-- A marker prime above `X` cannot divide a promoted factor whose base
prime is at most `X`, provided `2 ≤ X`. -/
theorem markerPrime_not_dvd_promotedCentralFactor
    {n X P p : ℕ} (hP : P.Prime) (hp : p.Prime)
    (hXTwo : 2 ≤ X) (hPLarge : X < P) (hpSmall : p ≤ X) :
    ¬ P ∣ promotedCentralFactor n p := by
  intro hdiv
  rcases prime_dvd_promotedCentralFactor hp hP hdiv with hP2 | hPp
  · omega
  · omega







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorProduct -/
section


/-!
# Exact product of all three central-anchor families

This file isolates the finite algebra behind the full central-anchor lemma.
For every large central prime, a cofactor choice is required to follow either
its row-zero route or its stationary carry row.  The resulting marker factors
are combined with every promoted low prime-power block.  Their product is
proved to be the central binomial coefficient times the literal cofactor and
promotion divisor.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







theorem routedCentralCofactor_mem_centralInterval
    {n p q : ℕ} (hq : IsRoutedCentralCofactor n p q) :
    p * q ∈ Finset.Ioc n (2 * n) := by
  rcases hq with hzero | ⟨r, _hrPos, _hr, hpRow, hqLower, hqUpper⟩
  · simpa only [hzero.2.2, mul_one] using
      (show p ∈ Finset.Ioc n (2 * n) from
        Finset.mem_Ioc.mpr ⟨hzero.1, hzero.2.1⟩)
  · exact stationaryPrimeLayer_mul_cofactor_mem_centralInterval
      hpRow hqLower hqUpper









theorem largeCentralAnchor_mem_centralInterval
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n X) :
    largeCentralAnchor q p ∈ Finset.Ioc n (2 * n) := by
  exact routedCentralCofactor_mem_centralInterval (hq p hp)























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorDivisorSupport -/
section


/-!
# Prime support and valuations of the central-anchor divisor

The exact anchor product introduces only the promotion power of two and the
chosen carry cofactors.  This file makes that assertion literal at every
prime, so later allocation estimates can be applied directly to the actual
integer divisor.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

theorem routedCentralCofactor_pos
    {n p q : ℕ} (hq : IsRoutedCentralCofactor n p q) : 0 < q := by
  rcases hq with hzero | ⟨r, _hrPos, _hr, _hpRow, hqLower, _hqUpper⟩
  · omega
  · omega

theorem largeCentralCofactor_pos
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n X) :
    0 < q p :=
  routedCentralCofactor_pos (hq p hp)











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CompleteRoughDecomposition -/
section


/-!
# Complete rough/smooth decomposition

The complete rough label retains exactly the prime-power coordinates above
`y`.  This file defines the complementary literal quotient and proves that
the two pieces recover the original natural number, with exact complementary
factorizations and no auxiliary decomposition hypothesis.
-/

namespace Erdos390.WholePaper

noncomputable section



/-! ## Positivity, divisibility, and product recovery -/

/-- A complete rough label is always positive, including for `a = 0`, when
the empty factorization gives label `1`. -/
theorem completeRoughLabel_pos (y a : ℕ) :
    0 < completeRoughLabel y a := by
  rw [completeRoughLabel]
  apply Nat.prod_pow_pos_of_zero_notMem_support
  rw [Finsupp.notMem_support_iff, completeRoughSignature_apply]
  simp

theorem completeRoughLabel_ne_zero (y a : ℕ) :
    completeRoughLabel y a ≠ 0 :=
  (completeRoughLabel_pos y a).ne'

/-- Literal Finsupp form of the high-prime factorization. -/
theorem completeRoughLabel_factorization_eq_filter_gt (y a : ℕ) :
    (completeRoughLabel y a).factorization =
      a.factorization.filter (fun p ↦ y < p) := by
  simpa only [completeRoughSignature] using
    completeRoughLabel_factorization y a

/-- Coordinate form of the exact high-prime factorization. -/
theorem completeRoughLabel_factorization_apply (y a p : ℕ) :
    (completeRoughLabel y a).factorization p =
      if y < p then a.factorization p else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
    (completeRoughLabel_factorization_eq_filter_gt y a)
  simpa only [Finsupp.filter_apply] using h

/-- The retained high-prime product is a literal divisor of the original
number. -/
theorem completeRoughLabel_dvd (y a : ℕ) :
    completeRoughLabel y a ∣ a := by
  by_cases ha : a = 0
  · rw [ha]
    exact dvd_zero _
  · rw [← Nat.factorization_le_iff_dvd
      (completeRoughLabel_ne_zero y a) ha,
      completeRoughLabel_factorization_eq_filter_gt]
    intro p
    rw [Finsupp.filter_apply]
    split_ifs <;> simp

/-- The requested multiplication direction: the original number is the
rough label times its literal complementary quotient. -/
theorem completeRough_decomposition (y a : ℕ) :
    a = completeRoughLabel y a * completeSmoothPart y a := by
  calc
    a = a / completeRoughLabel y a * completeRoughLabel y a :=
      (Nat.div_mul_cancel (completeRoughLabel_dvd y a)).symm
    _ = completeRoughLabel y a * (a / completeRoughLabel y a) :=
      Nat.mul_comm _ _
    _ = completeRoughLabel y a * completeSmoothPart y a := rfl



/-! ## The complementary low-prime factorization -/

/-- The quotient retains exactly the complementary coordinates `p ≤ y`. -/
theorem completeSmoothPart_factorization_eq_filter_le (y a : ℕ) :
    (completeSmoothPart y a).factorization =
      a.factorization.filter (fun p ↦ p ≤ y) := by
  rw [completeSmoothPart,
    Nat.factorization_div (completeRoughLabel_dvd y a),
    completeRoughLabel_factorization_eq_filter_gt]
  ext p
  simp only [Finsupp.filter_apply]
  by_cases hpLow : p ≤ y
  · have hpNotHigh : ¬y < p := Nat.not_lt_of_ge hpLow
    simp [hpLow, hpNotHigh]
  · have hpHigh : y < p := Nat.lt_of_not_ge hpLow
    simp [hpLow, hpHigh]

/-- Coordinate form of the exact low-prime factorization. -/
theorem completeSmoothPart_factorization_apply (y a p : ℕ) :
    (completeSmoothPart y a).factorization p =
      if p ≤ y then a.factorization p else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
    (completeSmoothPart_factorization_eq_filter_le y a)
  simpa only [Finsupp.filter_apply] using h

/-- Nonzero high-part coordinates lie strictly above the cutoff. -/
theorem completeRoughLabel_factorization_support
    {y a p : ℕ}
    (hp : (completeRoughLabel y a).factorization p ≠ 0) :
    y < p := by
  rw [completeRoughLabel_factorization_apply] at hp
  by_contra hpHigh
  simp [hpHigh] at hp

/-- Nonzero smooth-part coordinates lie weakly below the cutoff. -/
theorem completeSmoothPart_factorization_support
    {y a p : ℕ}
    (hp : (completeSmoothPart y a).factorization p ≠ 0) :
    p ≤ y := by
  rw [completeSmoothPart_factorization_apply] at hp
  by_contra hpLow
  simp [hpLow] at hp

/-- Every prime divisor of the complete rough label is above `y`. -/
theorem prime_dvd_completeRoughLabel_gt
    {y a p : ℕ} (hp : p.Prime)
    (hpDvd : p ∣ completeRoughLabel y a) :
    y < p := by
  have hfactorPos := hp.factorization_pos_of_dvd
    (completeRoughLabel_ne_zero y a) hpDvd
  exact completeRoughLabel_factorization_support hfactorPos.ne'

/-- For a positive original number, the complementary quotient is positive. -/
theorem completeSmoothPart_pos {y a : ℕ} (ha : 0 < a) :
    0 < completeSmoothPart y a := by
  rw [completeSmoothPart]
  apply Nat.div_pos
  · exact Nat.le_of_dvd ha (completeRoughLabel_dvd y a)
  · exact completeRoughLabel_pos y a

/-- For a positive original number, the complementary quotient is literally
`(y+1)`-smooth in Mathlib's positive-number convention. -/
theorem completeSmoothPart_mem_smoothNumbers
    {y a : ℕ} (ha : 0 < a) :
    completeSmoothPart y a ∈ Nat.smoothNumbers (y + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpDvd
  have hfactorPos := hp.factorization_pos_of_dvd
    (completeSmoothPart_pos ha).ne' hpDvd
  have hpLow : p ≤ y :=
    completeSmoothPart_factorization_support hfactorPos.ne'
  omega

/-! ## Uniqueness and the smooth-label criterion -/



/-- For positive `a`, the rough label is `1` exactly when `a` is
`(y+1)`-smooth. -/
theorem completeRoughLabel_eq_one_iff_mem_smoothNumbers
    {y a : ℕ} (ha : 0 < a) :
    completeRoughLabel y a = 1 ↔
      a ∈ Nat.smoothNumbers (y + 1) := by
  constructor
  · intro hlabel
    have haPart : a = completeSmoothPart y a := by
      simpa only [hlabel, one_mul] using
        completeRough_decomposition y a
    rw [haPart]
    exact completeSmoothPart_mem_smoothNumbers ha
  · intro haSmooth
    by_contra hlabel
    obtain ⟨p, hp, hpDvdLabel⟩ :=
      Nat.exists_prime_and_dvd hlabel
    have hpHigh : y < p :=
      prime_dvd_completeRoughLabel_gt hp hpDvdLabel
    have hpDvdA : p ∣ a :=
      hpDvdLabel.trans (completeRoughLabel_dvd y a)
    have hpLow :=
      (Nat.mem_smoothNumbers').mp haSmooth p hp hpDvdA
    omega



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorCutoff -/
section


/-!
# The fixed-prefix central-anchor cutoff

For a fixed prefix depth `R`, the paper splits the central prime blocks at
`n / (R + 1)`.  This file gives an explicit sufficient threshold for all
scale separations and then connects that literal cutoff directly to the
large-prime routing and central-anchor product APIs.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section





theorem centralAnchorCutoffThreshold_pos (R : ℕ) :
    0 < centralAnchorCutoffThreshold R := by
  simp [centralAnchorCutoffThreshold]

/-- At the explicit threshold, the cutoff is at least `4(R+1)`. -/
theorem four_mul_succ_le_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    4 * (R + 1) ≤ centralAnchorCutoff R n := by
  rw [centralAnchorCutoff, Nat.le_div_iff_mul_le (by omega)]
  simpa only [centralAnchorCutoffThreshold, pow_two, mul_assoc] using hn

/-- The cutoff lies strictly above every cofactor in rows `1,…,R`. -/
theorem two_mul_add_one_lt_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    2 * R + 1 < centralAnchorCutoff R n := by
  have hfour := four_mul_succ_le_centralAnchorCutoff hn
  omega





theorem two_le_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    2 ≤ centralAnchorCutoff R n := by
  have hsep := two_mul_add_one_lt_centralAnchorCutoff hn
  omega







/-- A prime above `n/(R+1)` has quotient row at most `R`. -/
theorem div_le_fixedPrefix_of_centralAnchorCutoff_lt
    {R n p : ℕ} (hp : centralAnchorCutoff R n < p) :
    n / p ≤ R := by
  have hpPos : 0 < p := by omega
  have hdiv : n / (R + 1) < p := by
    simpa only [centralAnchorCutoff] using hp
  have hnUpper : n < p * (R + 1) :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < R + 1)).1 hdiv
  have hrow : n / p < R + 1 :=
    (Nat.div_lt_iff_lt_mul hpPos).2 (by
      simpa only [Nat.mul_comm] using hnUpper)
  omega

theorem largeCentralPrime_div_le_fixedPrefix
    {R n p : ℕ}
    (hp : p ∈ largeCentralPrimes n (centralAnchorCutoff R n)) :
    n / p ≤ R :=
  div_le_fixedPrefix_of_centralAnchorCutoff_lt
    (largeCentralPrimes_gt hp)



/-- Every routed cofactor above the literal cutoff is in the fixed
cofactor prefix `[1,2R+1]`. -/
theorem largeCentralCofactor_le_fixedPrefix
    {R n : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n (centralAnchorCutoff R n)) :
    q p ≤ 2 * R + 1 := by
  rcases hq p hp with hzero |
      ⟨r, _hrPos, hr, _hpRow, _hqLower, hqUpper⟩
  · omega
  · have hrUpper : r ≤ R := by
      rw [hr]
      exact largeCentralPrime_div_le_fixedPrefix hp
    omega





















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardCapacityReduction -/
section


/-!
# Canonical rough-row guard capacity reduction

This file closes the finite part of the three guard-local obligations exposed
by `BankPaperCanonicalGuardLocalRowLedger`.

For every non-smooth complete rough row, at most one central anchor, one bank
base, and one bank alternate can occur.  Thus the literal local guard census
is at most three.  Removing those three possible coordinates from a raw broad
pool gives the guarded-pool capacity, and containment of the guarded broad
pool in the guarded row gives the postcharge capacity.

The only non-finite input left visible is `RoughCanonicalActiveRawBroadSurplus`:
the raw broad pool must contain the larger of the requested pool minimum and
the literal upper-row target, plus the three-coordinate guard slack.  This is
the exact de Bruijn--Saias lower-bound consequence still needed from the
analytic rough-row argument; it contains no selector or bookkeeping premise.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Complete rough labels remember retained prime divisors -/

/-- A prime divisor above the smooth cutoff is retained in the complete
rough label. -/
theorem prime_dvd_completeRoughLabel_of_cutoff_lt
    {y a p : Nat} (hp : p.Prime) (hyp : y < p)
    (ha : a ≠ 0) (hpa : p ∣ a) :
    p ∣ completeRoughLabel y a := by
  apply (hp.dvd_iff_one_le_factorization
    (completeRoughLabel_ne_zero y a)).mpr
  rw [completeRoughLabel_factorization_apply, if_pos hyp]
  exact (hp.dvd_iff_one_le_factorization ha).mp hpa

/-- A promoted central factor whose base prime is below the smooth cutoff
has trivial complete rough label. -/
theorem completeRoughLabel_promotedCentralFactor_eq_one_of_base_le
    {n y p : Nat} (hn : 0 < n) (hyTwo : 2 <= y)
    (hp : p.Prime) (hpy : p <= y) :
    completeRoughLabel y (promotedCentralFactor n p) = 1 := by
  apply (completeRoughLabel_eq_one_iff_mem_smoothNumbers
    (Nat.zero_lt_of_lt
      (promotedCentralFactor_gt (n := n) (p := p) hn))).2
  rw [Nat.mem_smoothNumbers']
  intro ell hell hellDvd
  rcases prime_dvd_promotedCentralFactor hp hell hellDvd with
      rfl | rfl
  · omega
  · omega

/-! ## One central anchor in every non-smooth row -/

/-- The full central-anchor map is injective after passing to any nontrivial
complete rough label whose cutoff lies below the large-marker cutoff.

Promoted anchors with base at most `y` lie in the smooth row.  A retained
promoted base prime recovers that promoted anchor.  For a routed large anchor,
its marker prime is retained and is too large to divide any other promoted
anchor or any other routed cofactor. -/
theorem fullCentralAnchors_completeRoughLabel_injective_of_ne_one
    {depth n y : Nat} {q : Nat -> Nat}
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyTwo : 2 <= y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (hq : IsLargeCentralCofactorChoice n
      (centralAnchorCutoff depth n) q)
    {a b : Nat}
    (ha : a ∈ fullCentralAnchors n (centralAnchorCutoff depth n) q)
    (hb : b ∈ fullCentralAnchors n (centralAnchorCutoff depth n) q)
    (haNontrivial : completeRoughLabel y a ≠ 1)
    (hab : completeRoughLabel y a = completeRoughLabel y b) :
    a = b := by
  have hn : 0 < n :=
    (centralAnchorCutoffThreshold_pos depth).trans_le hnCutoff
  rw [fullCentralAnchors] at ha hb
  rcases Finset.mem_union.mp ha with haPromoted | haLarge
  · obtain ⟨p, hpMem, rfl⟩ := Finset.mem_image.mp haPromoted
    have hpPrime := residualCentralPrimes_prime hpMem
    have hpSmall := residualCentralPrimes_le hpMem
    rcases Finset.mem_union.mp hb with hbPromoted | hbLarge
    · obtain ⟨p', hp'Mem, rfl⟩ := Finset.mem_image.mp hbPromoted
      have hp'Prime := residualCentralPrimes_prime hp'Mem
      have hpHigh : y < p := by
        by_contra hpNotHigh
        have hpLow : p <= y := Nat.le_of_not_gt hpNotHigh
        exact haNontrivial
          (completeRoughLabel_promotedCentralFactor_eq_one_of_base_le
            hn hyTwo hpPrime hpLow)
      have hpDvdPromoted : p ∣ promotedCentralFactor n p := by
        unfold promotedCentralFactor promotedBlock centralPrimeBlock
        exact dvd_mul_of_dvd_right
          (dvd_pow_self p
            (residualCentralPrimes_exponent_pos hpMem).ne') _
      have hpDvdLabel :
          p ∣ completeRoughLabel y (promotedCentralFactor n p) :=
        prime_dvd_completeRoughLabel_of_cutoff_lt hpPrime hpHigh
          (Nat.zero_lt_of_lt (promotedCentralFactor_gt hn)).ne'
          hpDvdPromoted
      have hpDvdOther : p ∣ promotedCentralFactor n p' := by
        apply hpDvdLabel.trans
        rw [hab]
        exact completeRoughLabel_dvd y (promotedCentralFactor n p')
      rcases prime_dvd_promotedCentralFactor hp'Prime hpPrime hpDvdOther with
          hpTwo | hpp'
      · omega
      · subst p'
        rfl
    · obtain ⟨P, hPMem, rfl⟩ := Finset.mem_image.mp hbLarge
      have hPPrime := largeCentralPrimes_prime hPMem
      have hPHigh : y < P :=
        hyCutoff.trans (largeCentralPrimes_gt hPMem)
      have hPAnchorPos : 0 < largeCentralAnchor q P := by
        exact Nat.zero_lt_of_lt
          (Finset.mem_Ioc.mp
            (largeCentralAnchor_mem_centralInterval hq hPMem)).1
      have hPDvdLabel :
          P ∣ completeRoughLabel y (largeCentralAnchor q P) :=
        prime_dvd_completeRoughLabel_of_cutoff_lt hPPrime hPHigh
          hPAnchorPos.ne' (by
            exact dvd_mul_right P (q P))
      have hPDvdPromoted : P ∣ promotedCentralFactor n p := by
        apply hPDvdLabel.trans
        rw [← hab]
        exact completeRoughLabel_dvd y (promotedCentralFactor n p)
      exact (markerPrime_not_dvd_promotedCentralFactor hPPrime hpPrime
        (two_le_centralAnchorCutoff hnCutoff)
        (largeCentralPrimes_gt hPMem) hpSmall hPDvdPromoted).elim
  · obtain ⟨P, hPMem, rfl⟩ := Finset.mem_image.mp haLarge
    have hPPrime := largeCentralPrimes_prime hPMem
    have hPHigh : y < P :=
      hyCutoff.trans (largeCentralPrimes_gt hPMem)
    have hPAnchorPos : 0 < largeCentralAnchor q P := by
      exact Nat.zero_lt_of_lt
        (Finset.mem_Ioc.mp
          (largeCentralAnchor_mem_centralInterval hq hPMem)).1
    have hPDvdLabel :
        P ∣ completeRoughLabel y (largeCentralAnchor q P) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hPPrime hPHigh
        hPAnchorPos.ne' (by exact dvd_mul_right P (q P))
    rcases Finset.mem_union.mp hb with hbPromoted | hbLarge
    · obtain ⟨p, hpMem, rfl⟩ := Finset.mem_image.mp hbPromoted
      have hpPrime := residualCentralPrimes_prime hpMem
      have hpSmall := residualCentralPrimes_le hpMem
      have hPDvdPromoted : P ∣ promotedCentralFactor n p := by
        apply hPDvdLabel.trans
        rw [hab]
        exact completeRoughLabel_dvd y (promotedCentralFactor n p)
      exact (markerPrime_not_dvd_promotedCentralFactor hPPrime hpPrime
        (two_le_centralAnchorCutoff hnCutoff)
        (largeCentralPrimes_gt hPMem) hpSmall hPDvdPromoted).elim
    · obtain ⟨P', hP'Mem, rfl⟩ := Finset.mem_image.mp hbLarge
      have hP'Prime := largeCentralPrimes_prime hP'Mem
      have hPDvdOther : P ∣ largeCentralAnchor q P' := by
        apply hPDvdLabel.trans
        rw [hab]
        exact completeRoughLabel_dvd y (largeCentralAnchor q P')
      rw [largeCentralAnchor] at hPDvdOther
      rcases hPPrime.dvd_mul.mp hPDvdOther with hPP' | hPq
      · have hmarker : P = P' :=
          (Nat.prime_dvd_prime_iff_eq hPPrime hP'Prime).mp hPP'
        subst P'
        rfl
      · have hqPos : 0 < q P' :=
          largeCentralCofactor_pos hq hP'Mem
        have hPLeQ : P <= q P' := Nat.le_of_dvd hqPos hPq
        have hqLe : q P' <= 2 * depth + 1 :=
          largeCentralCofactor_le_fixedPrefix hq hP'Mem
        have hprefixCutoff :=
          two_mul_add_one_lt_centralAnchorCutoff hnCutoff
        have hcutoffP := largeCentralPrimes_gt hPMem
        omega



namespace BankPaperRealization

/-! ## One base and one alternate in every bank row -/



























/-! ## The literal three-coordinate local census -/





/-! ## Guarded broad-pool and postcharge capacities -/







/-! ## The single remaining analytic raw-pool input -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {depth n y : Nat} {q : Nat → Nat},
  LE.le.{0} (Erdos390.WholePaper.centralAnchorCutoffThreshold depth) n →
    LE.le.{0} (2 : Nat) y →
      LT.lt.{0} y (Erdos390.WholePaper.centralAnchorCutoff depth n) →
        Erdos390.WholePaper.IsLargeCentralCofactorChoice n (Erdos390.WholePaper.centralAnchorCutoff depth n) q →
          ∀ {a b : Nat},
            Membership.mem.{0, 0}
                (Erdos390.WholePaper.fullCentralAnchors n (Erdos390.WholePaper.centralAnchorCutoff depth n) q) a →
              Membership.mem.{0, 0}
                  (Erdos390.WholePaper.fullCentralAnchors n (Erdos390.WholePaper.centralAnchorCutoff depth n) q) b →
                Ne.{1} (Erdos390.WholePaper.completeRoughLabel y a) (1 : Nat) →
                  Eq.{1} (Erdos390.WholePaper.completeRoughLabel y a) (Erdos390.WholePaper.completeRoughLabel y b) →
                    Eq.{1} a b := by
  exact @Erdos390.WholePaper.fullCentralAnchors_completeRoughLabel_injective_of_ne_one
