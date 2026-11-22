-- Prove2me | solution 1 for Erdos390.WholePaper.guardedCentralAnchorCertificate_of_changeCost
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:52:55.608884+00:00
-- url     : https://prove2.me/submissions/87747d15-c534-4361-b2fb-e1ff060987c4

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007

/- Source module: Erdos390.WholePaper.Complement -/
section


/-!
# Exact complement formulation

This proves the complement lemma immediately following the main theorem in
the paper.  All divisions occur in `ℚ`; the proof also exports the integral
cross-multiplication form used by later valuation arguments.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section





/-- Product of every integer in `(n,M]`, without truncated division. -/
theorem factorInterval_prod_mul_factorial {n M : ℕ} (hnM : n ≤ M) :
    (factorInterval n M).prod id * n.factorial = M.factorial := by
  induction M, hnM using Nat.le_induction with
  | base => simp [factorInterval]
  | succ M hnM ih =>
      rw [factorInterval, Finset.prod_Ioc_succ_top hnM, Nat.factorial_succ]
      change ((Finset.Ioc n M).prod id * (M + 1)) * n.factorial =
        (M + 1) * M.factorial
      calc
        ((Finset.Ioc n M).prod id * (M + 1)) * n.factorial =
            (M + 1) * ((Finset.Ioc n M).prod id * n.factorial) := by
              ac_rfl
        _ = (M + 1) * M.factorial := by
          rw [show (Finset.Ioc n M).prod id * n.factorial = M.factorial by
            simpa [factorInterval] using ih]







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.PrimeLayers -/
section


/-!
# Exact prime-layer arithmetic for the lower bound

This file contains only finite identities.  Analytic estimates for the
cardinalities of the layers are kept separate.  Cross-multiplied endpoint
conditions avoid all ambiguity from natural-number division at rational
endpoints.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section











/-- Above the square-root cutoff, Legendre's sum has only its first term. -/
theorem factorial_factorization_eq_div_of_lt_sq {m p : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmSq : m < p ^ 2) :
    m.factorial.factorization p = m / p := by
  rw [Nat.factorization_factorial hp (Nat.log_lt_of_lt_pow hm.ne' hmSq)]
  simp





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.LargePrimeCollision -/
section


/-! Exact collision exclusion for the thirteen large-prime layers. -/

namespace Erdos390.WholePaper

/-- An integer below `L²` cannot contain two distinct primes at least `L`. -/
theorem not_two_distinct_large_primes_dvd
    {p q a L B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hLp : L ≤ p) (hLq : L ≤ q)
    (ha : 0 < a) (haB : a ≤ B) (hBL : B < L * L) :
    ¬(p ∣ a ∧ q ∣ a) := by
  rintro ⟨hpa, hqa⟩
  have hpqa : p * q ∣ a := hp.dvd_mul_of_dvd_ne hpq hq hpa hqa
  have hpq_le : p * q ≤ a := Nat.le_of_dvd ha hpqa
  have hLL_le : L * L ≤ p * q := Nat.mul_le_mul hLp hLq
  omega



end Erdos390.WholePaper

end

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

/- Source module: Erdos390.WholePaper.CentralExtension -/
section


/-!
# Extension to the central binomial endpoint

This is the exact preliminary construction in the first lower-bound lemma:
a complement representation ending at `M ≤ 2n` is extended by every integer
in `(M,2n]`, producing a distinct-factor representation of `choose (2n) n`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section









theorem centralChoose_mul_factorial_sq (n : ℕ) :
    Nat.choose (2 * n) n * n.factorial ^ 2 = (2 * n).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  have hsub : 2 * n - n = n := by omega
  simpa [hsub, pow_two, mul_assoc] using h







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TailValuationCore -/
section


/-! # Per-prime factorial-tail valuation estimates -/

namespace Erdos390.WholePaper

noncomputable section







theorem centralFactorialValuation_eq_choose_add {n p : ℕ} :
    (2 * n).factorial.factorization p =
      (Nat.choose (2 * n) n).factorization p +
        2 * n.factorial.factorization p := by
  have hchoosePos : 0 < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  have hfactorization := congrArg Nat.factorization
    (centralChoose_mul_factorial_sq n)
  rw [Nat.factorization_mul hchoosePos.ne'
      (pow_ne_zero 2 (Nat.factorial_ne_zero n)),
    Nat.factorization_pow] at hfactorization
  have hcoordinate := congrArg (fun v : ℕ →₀ ℕ ↦ v p) hfactorization
  simpa only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
    Nat.cast_ofNat] using hcoordinate.symm







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





/-- Promotion does not change the valuation at an odd base prime. -/
theorem promotedCentralFactor_factorization_odd
    {n p : ℕ} (hp : p.Prime) (hpOdd : p ≠ 2) :
    (promotedCentralFactor n p).factorization p =
      (Nat.choose (2 * n) n).factorization p := by
  have htwoPow : 2 ^ promotionExponent n (centralPrimeBlock n p) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hpPow : centralPrimeBlock n p ≠ 0 :=
    (centralPrimeBlock_pos n p).ne'
  have htwoPrime : Nat.Prime 2 := by norm_num
  have htwoFac :
      (2 ^ promotionExponent n (centralPrimeBlock n p)).factorization p = 0 := by
    rw [htwoPrime.factorization_pow]
    simp [Ne.symm hpOdd]
  rw [promotedCentralFactor, promotedBlock,
    Nat.factorization_mul htwoPow hpPow]
  simp only [Finsupp.add_apply]
  rw [htwoFac, centralPrimeBlock, Nat.factorization_pow_self hp]
  simp

/-- At an odd prime `p`, a promoted factor based at a different prime `q`
has zero `p`-valuation. -/
theorem promotedCentralFactor_factorization_cross
    {n p q : ℕ} (hq : q.Prime) (hpOdd : p ≠ 2) (hpq : p ≠ q) :
    (promotedCentralFactor n q).factorization p = 0 := by
  have htwoPow : 2 ^ promotionExponent n (centralPrimeBlock n q) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hqPow : centralPrimeBlock n q ≠ 0 :=
    (centralPrimeBlock_pos n q).ne'
  have htwoPrime : Nat.Prime 2 := by norm_num
  have htwoFac :
      (2 ^ promotionExponent n (centralPrimeBlock n q)).factorization p = 0 := by
    rw [htwoPrime.factorization_pow]
    simp [Ne.symm hpOdd]
  have hqFac : (centralPrimeBlock n q).factorization p = 0 := by
    rw [centralPrimeBlock, hq.factorization_pow]
    simp [Ne.symm hpq]
  rw [promotedCentralFactor, promotedBlock,
    Nat.factorization_mul htwoPow hqPow]
  simp only [Finsupp.add_apply]
  rw [htwoFac, hqFac, add_zero]



/-- Promoted factors attached to distinct primes with positive central
exponent are distinct. -/
theorem promotedCentralFactor_injective_on_positive_support
    {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpExponent : 0 < (Nat.choose (2 * n) n).factorization p)
    (hqExponent : 0 < (Nat.choose (2 * n) n).factorization q)
    (hfactor : promotedCentralFactor n p = promotedCentralFactor n q) :
    p = q := by
  by_contra hpq
  by_cases hpTwo : p = 2
  · have hqOdd : q ≠ 2 := by
      intro hqTwo
      apply hpq
      exact hpTwo.trans hqTwo.symm
    have hcoordinate := congrArg (fun a : ℕ ↦ a.factorization q) hfactor
    change (promotedCentralFactor n p).factorization q =
      (promotedCentralFactor n q).factorization q at hcoordinate
    rw [promotedCentralFactor_factorization_cross
        (p := q) (q := p) hp hqOdd (Ne.symm hpq),
      promotedCentralFactor_factorization_odd hq hqOdd] at hcoordinate
    omega
  · have hcoordinate := congrArg (fun a : ℕ ↦ a.factorization p) hfactor
    change (promotedCentralFactor n p).factorization p =
      (promotedCentralFactor n q).factorization p at hcoordinate
    rw [promotedCentralFactor_factorization_odd hp hpTwo,
      promotedCentralFactor_factorization_cross
        (p := p) (q := q) hq hpTwo hpq] at hcoordinate
    omega

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

theorem promotedCentralFactor_injOn_residualCentralPrimes (n X : ℕ) :
    Set.InjOn (promotedCentralFactor n) (residualCentralPrimes n X) := by
  intro p hp q hq hpq
  exact promotedCentralFactor_injective_on_positive_support
    (residualCentralPrimes_prime hp) (residualCentralPrimes_prime hq)
    (residualCentralPrimes_exponent_pos hp)
    (residualCentralPrimes_exponent_pos hq) hpq



theorem residualPromotedFactors_subset_centralInterval
    {n X : ℕ} (hn : 0 < n) :
    residualPromotedFactors n X ⊆ Finset.Ioc n (2 * n) := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  exact promotedCentralFactor_mem_centralInterval hn

/-- Exact product identity for the promoted residual family. -/
theorem residualPromotedFactors_prod (n X : ℕ) :
    (residualPromotedFactors n X).prod id =
      2 ^ residualPromotionCost n X *
        (residualCentralPrimes n X).prod (centralPrimeBlock n) := by
  rw [residualPromotedFactors,
    Finset.prod_image
      (promotedCentralFactor_injOn_residualCentralPrimes n X)]
  simp only [id_eq, promotedCentralFactor, promotedBlock]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rfl

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

theorem residualCentralPrimes_disjoint_largeCentralPrimes (n X : ℕ) :
    Disjoint (residualCentralPrimes n X) (largeCentralPrimes n X) := by
  rw [Finset.disjoint_left]
  intro p hpLow hpHigh
  exact (not_lt_of_ge (residualCentralPrimes_le hpLow))
    (largeCentralPrimes_gt hpHigh)

theorem residualCentralPrimes_union_largeCentralPrimes (n X : ℕ) :
    residualCentralPrimes n X ∪ largeCentralPrimes n X =
      (Nat.choose (2 * n) n).primeFactors := by
  ext p
  simp only [residualCentralPrimes, largeCentralPrimes,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  · intro hp
    by_cases hle : p ≤ X
    · exact Or.inl ⟨hp, hle⟩
    · exact Or.inr ⟨hp, by omega⟩

/-- The product of all complete central prime-power blocks is exactly the
central binomial coefficient. -/
theorem centralPrimeBlocks_prod_all (n : ℕ) :
    ((Nat.choose (2 * n) n).primeFactors).prod (centralPrimeBlock n) =
      Nat.choose (2 * n) n := by
  have hchoose : Nat.choose (2 * n) n ≠ 0 :=
    (Nat.choose_pos (by omega)).ne'
  simpa only [centralPrimeBlock, Nat.support_factorization] using
    Nat.factorization_prod_pow_eq_self hchoose

/-- Exact multiplicative split at an arbitrary cutoff. -/
theorem residual_mul_largeCentralPrimeBlocks (n X : ℕ) :
    (residualCentralPrimes n X).prod (centralPrimeBlock n) *
        (largeCentralPrimes n X).prod (centralPrimeBlock n) =
      Nat.choose (2 * n) n := by
  rw [← Finset.prod_union
    (residualCentralPrimes_disjoint_largeCentralPrimes n X),
    residualCentralPrimes_union_largeCentralPrimes,
    centralPrimeBlocks_prod_all]

/-- Promoting all low blocks changes the complete central product by exactly
`2^K` and leaves the high blocks untouched. -/
theorem residualPromoted_mul_largeCentralPrimeBlocks (n X : ℕ) :
    (residualPromotedFactors n X).prod id *
        (largeCentralPrimes n X).prod (centralPrimeBlock n) =
      2 ^ residualPromotionCost n X * Nat.choose (2 * n) n := by
  rw [residualPromotedFactors_prod]
  calc
    (2 ^ residualPromotionCost n X *
          (residualCentralPrimes n X).prod (centralPrimeBlock n)) *
        (largeCentralPrimes n X).prod (centralPrimeBlock n) =
      2 ^ residualPromotionCost n X *
        ((residualCentralPrimes n X).prod (centralPrimeBlock n) *
          (largeCentralPrimes n X).prod (centralPrimeBlock n)) := by
        ac_rfl
    _ = 2 ^ residualPromotionCost n X * Nat.choose (2 * n) n := by
      rw [residual_mul_largeCentralPrimeBlocks]

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

/- Source module: Erdos390.WholePaper.LargeCentralPrimeRouting -/
section


/-!
# Routing every large central prime to a carry row or row zero

Above a square-root cutoff, Legendre's formula has only its first term.
Thus every large prime divisor of the central binomial coefficient occurs
once, and its quotient row `n / p` determines its unique anchor family.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- If a prime occurs in the central binomial coefficient and `p^2 > 2n`,
then its valuation is one and the two floor quotients differ by one carry. -/
theorem centralChoose_largePrime_carry
    {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpExponent : 0 < (Nat.choose (2 * n) n).factorization p)
    (hpSq : 2 * n < p ^ 2) :
    (Nat.choose (2 * n) n).factorization p = 1 ∧
      (2 * n) / p = 2 * (n / p) + 1 := by
  let r := n / p
  have hnSq : n < p ^ 2 := by omega
  have hnFac : n.factorial.factorization p = r := by
    simpa only [r] using
      factorial_factorization_eq_div_of_lt_sq hp hn hnSq
  have htwoFac : (2 * n).factorial.factorization p = (2 * n) / p := by
    exact factorial_factorization_eq_div_of_lt_sq hp (by omega) hpSq
  have hnUpper : n < p * (r + 1) := by
    simpa only [r] using Nat.lt_mul_div_succ n hp.pos
  have htwoUpper : 2 * n < (2 * r + 2) * p := by
    calc
      2 * n < 2 * (p * (r + 1)) :=
        (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hnUpper
      _ = (2 * r + 2) * p := by ring
  have hdivUpper : (2 * n) / p ≤ 2 * r + 1 := by
    have hlt : (2 * n) / p < 2 * r + 2 :=
      (Nat.div_lt_iff_lt_mul hp.pos).2 htwoUpper
    omega
  have hcentral := centralFactorialValuation_eq_choose_add
    (n := n) (p := p)
  rw [hnFac, htwoFac] at hcentral
  constructor <;> omega

/-- A cutoff strictly below `p` transfers its square bound to `p`. -/
theorem two_mul_lt_prime_sq_of_cutoff
    {n X p : ℕ} (hXsq : 2 * n < X ^ 2) (hXp : X < p) :
    2 * n < p ^ 2 := by
  have hPow : X ^ 2 < p ^ 2 := by
    rw [pow_two, pow_two]
    exact (Nat.mul_le_mul_left X hXp.le).trans_lt
      ((Nat.mul_lt_mul_right (by omega : 0 < p)).2 hXp)
  exact hXsq.trans hPow

/-- Every large central prime is routed exactly either to the row-zero
interval `(n,2n]` or to its positive stationary carry row. -/
theorem largeCentralPrime_rowZero_or_stationary
    {n X p : ℕ} (hn : 0 < n) (hXsq : 2 * n < X ^ 2)
    (hpMem : p ∈ largeCentralPrimes n X) :
    (Nat.choose (2 * n) n).factorization p = 1 ∧
      ((n < p ∧ p ≤ 2 * n) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r = n / p ∧
          p ∈ stationaryPrimeLayer n r) := by
  have hpPrime := largeCentralPrimes_prime hpMem
  have hpFactors : p ∈ (Nat.choose (2 * n) n).primeFactors :=
    (Finset.mem_filter.mp hpMem).1
  have hpExponent : 0 < (Nat.choose (2 * n) n).factorization p := by
    exact hpPrime.factorization_pos_of_dvd
      (Nat.choose_pos (by omega)).ne'
      (Nat.dvd_of_mem_primeFactors hpFactors)
  have hpSq := two_mul_lt_prime_sq_of_cutoff hXsq
    (largeCentralPrimes_gt hpMem)
  obtain ⟨hpOne, hfloor⟩ :=
    centralChoose_largePrime_carry hn hpPrime hpExponent hpSq
  refine ⟨hpOne, ?_⟩
  let r := n / p
  have hnUpper : n < p * (r + 1) := by
    simpa only [r] using Nat.lt_mul_div_succ n hpPrime.pos
  by_cases hrZero : r = 0
  · left
    constructor
    · simpa only [hrZero, zero_add, mul_one] using hnUpper
    · have hOneLe : 1 ≤ (2 * n) / p := by
        rw [hfloor]
        omega
      have hpLe := (Nat.le_div_iff_mul_le hpPrime.pos).1 hOneLe
      simpa only [one_mul] using hpLe
  · right
    refine ⟨r, Nat.one_le_iff_ne_zero.mpr hrZero, rfl, ?_⟩
    rw [mem_stationaryPrimeLayer]
    refine ⟨hpPrime, hnUpper, ?_⟩
    have hrowLe : 2 * r + 1 ≤ (2 * n) / p := by omega
    have hmul := (Nat.le_div_iff_mul_le hpPrime.pos).1 hrowLe
    simpa only [Nat.mul_comm] using hmul

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

/-- No prefix-style marker--cofactor product can collide with a promoted
residual factor. -/
theorem marker_mul_ne_promotedCentralFactor
    {n X P q p : ℕ} (hP : P.Prime) (hp : p.Prime)
    (hXTwo : 2 ≤ X) (hPLarge : X < P) (hpSmall : p ≤ X) :
    P * q ≠ promotedCentralFactor n p := by
  intro heq
  apply markerPrime_not_dvd_promotedCentralFactor hP hp hXTwo hPLarge hpSmall
  rw [← heq]
  exact dvd_mul_right P q





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

/-- The square separation prevents two different large marker primes from
occurring in the same central-interval integer. -/
theorem largeCentralAnchor_injOn
    {n X : ℕ} {q : ℕ → ℕ} (hXsq : 2 * n < X ^ 2)
    (hq : IsLargeCentralCofactorChoice n X q) :
    Set.InjOn (largeCentralAnchor q) (largeCentralPrimes n X) := by
  intro p hp p' hp' heq
  by_contra hpp'
  have hpPrime := largeCentralPrimes_prime hp
  have hp'Prime := largeCentralPrimes_prime hp'
  have haMem := largeCentralAnchor_mem_centralInterval hq hp
  have haPos : 0 < largeCentralAnchor q p := by
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp haMem).1
  have haUpper : largeCentralAnchor q p ≤ 2 * n :=
    (Finset.mem_Ioc.mp haMem).2
  apply not_two_distinct_large_primes_dvd
    hpPrime hp'Prime hpp'
    (largeCentralPrimes_gt hp).le (largeCentralPrimes_gt hp').le
    haPos haUpper (by simpa only [pow_two] using hXsq)
  constructor
  · exact dvd_mul_right p (q p)
  · rw [heq]
    exact dvd_mul_right p' (q p')

theorem largeCentralAnchors_subset_centralInterval
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    largeCentralAnchors n X q ⊆ Finset.Ioc n (2 * n) := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  exact largeCentralAnchor_mem_centralInterval hq hp



theorem largeCentralAnchors_prod
    {n X : ℕ} {q : ℕ → ℕ} (hXsq : 2 * n < X ^ 2)
    (hq : IsLargeCentralCofactorChoice n X q) :
    (largeCentralAnchors n X q).prod id =
      (largeCentralPrimes n X).prod id *
        largeCentralCofactorProduct n X q := by
  rw [largeCentralAnchors,
    Finset.prod_image (largeCentralAnchor_injOn hXsq hq)]
  simp only [id_eq, largeCentralAnchor, largeCentralCofactorProduct,
    Finset.prod_mul_distrib]

theorem largeCentralPrimeBlocks_eq_primeProduct
    {n X : ℕ} (hn : 0 < n) (hXsq : 2 * n < X ^ 2) :
    (largeCentralPrimes n X).prod (centralPrimeBlock n) =
      (largeCentralPrimes n X).prod id := by
  apply Finset.prod_congr rfl
  intro p hp
  have hpOne :=
    (largeCentralPrime_rowZero_or_stationary hn hXsq hp).1
  simp only [centralPrimeBlock, hpOne, pow_one, id_eq]





theorem residualPromotedFactors_disjoint_largeCentralAnchors
    {n X : ℕ} {q : ℕ → ℕ} (hXTwo : 2 ≤ X) :
    Disjoint (residualPromotedFactors n X)
      (largeCentralAnchors n X q) := by
  rw [Finset.disjoint_left]
  intro a haLow haHigh
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp haLow
  obtain ⟨P, hP, hEq⟩ := Finset.mem_image.mp haHigh
  have hpPrime := residualCentralPrimes_prime hp
  have hPPrime := largeCentralPrimes_prime hP
  apply marker_mul_ne_promotedCentralFactor
    hPPrime hpPrime hXTwo (largeCentralPrimes_gt hP)
      (residualCentralPrimes_le hp)
  simpa only [largeCentralAnchor] using hEq

theorem fullCentralAnchors_subset_centralInterval
    {n X : ℕ} {q : ℕ → ℕ} (hn : 0 < n)
    (hq : IsLargeCentralCofactorChoice n X q) :
    fullCentralAnchors n X q ⊆ Finset.Ioc n (2 * n) := by
  intro a ha
  rcases Finset.mem_union.mp ha with haLow | haHigh
  · exact residualPromotedFactors_subset_centralInterval hn haLow
  · exact largeCentralAnchors_subset_centralInterval hq haHigh



/-- Literal exact product identity for the complete central-anchor set. -/
theorem fullCentralAnchors_prod
    {n X : ℕ} {q : ℕ → ℕ} (hn : 0 < n) (hXTwo : 2 ≤ X)
    (hXsq : 2 * n < X ^ 2)
    (hq : IsLargeCentralCofactorChoice n X q) :
    (fullCentralAnchors n X q).prod id =
      Nat.choose (2 * n) n * centralAnchorDivisor n X q := by
  have hcentral := residualPromoted_mul_largeCentralPrimeBlocks n X
  rw [largeCentralPrimeBlocks_eq_primeProduct hn hXsq] at hcentral
  rw [fullCentralAnchors,
    Finset.prod_union
      (residualPromotedFactors_disjoint_largeCentralAnchors hXTwo),
    largeCentralAnchors_prod hXsq hq]
  calc
    (residualPromotedFactors n X).prod id *
        ((largeCentralPrimes n X).prod id *
          largeCentralCofactorProduct n X q) =
      ((residualPromotedFactors n X).prod id *
        (largeCentralPrimes n X).prod id) *
          largeCentralCofactorProduct n X q := by ac_rfl
    _ = (2 ^ residualPromotionCost n X * Nat.choose (2 * n) n) *
          largeCentralCofactorProduct n X q := by rw [hcentral]
    _ = Nat.choose (2 * n) n * centralAnchorDivisor n X q := by
      simp only [centralAnchorDivisor]
      ac_rfl

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

theorem largeCentralCofactorProduct_pos
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    0 < largeCentralCofactorProduct n X q := by
  exact Finset.prod_pos fun p hp ↦ largeCentralCofactor_pos hq hp

theorem centralAnchorDivisor_pos
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    0 < centralAnchorDivisor n X q := by
  exact mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) _)
    (largeCentralCofactorProduct_pos hq)

/-- Every prime divisor is either the promotion prime `2` or divides one of
the literal chosen cofactors. -/
theorem prime_dvd_centralAnchorDivisor
    {n X ℓ : ℕ} {q : ℕ → ℕ} (hℓ : ℓ.Prime)
    (hdiv : ℓ ∣ centralAnchorDivisor n X q) :
    ℓ = 2 ∨ ∃ p ∈ largeCentralPrimes n X, ℓ ∣ q p := by
  rw [centralAnchorDivisor] at hdiv
  rcases hℓ.dvd_mul.mp hdiv with htwo | hcofactor
  · left
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp
      (hℓ.dvd_of_dvd_pow htwo)
  · right
    simpa only [largeCentralCofactorProduct] using
      (hℓ.prime.dvd_finset_prod_iff q).mp hcofactor

/-- A uniform cofactor bound gives a literal finite prime support. -/
theorem prime_dvd_centralAnchorDivisor_le
    {n X B ℓ : ℕ} {q : ℕ → ℕ}
    (hqChoice : IsLargeCentralCofactorChoice n X q)
    (hqBound : ∀ p ∈ largeCentralPrimes n X, q p ≤ B)
    (hℓ : ℓ.Prime) (hdiv : ℓ ∣ centralAnchorDivisor n X q) :
    ℓ ≤ max 2 B := by
  rcases prime_dvd_centralAnchorDivisor hℓ hdiv with rfl | ⟨p, hp, hℓq⟩
  · exact le_max_left 2 B
  · have hℓLe : ℓ ≤ q p :=
      Nat.le_of_dvd (largeCentralCofactor_pos hqChoice hp) hℓq
    exact (hℓLe.trans (hqBound p hp)).trans (le_max_right 2 B)

/-- Exact valuation ledger: promotion contributes only at `2`, and every
other contribution is the sum of cofactor valuations. -/
theorem centralAnchorDivisor_factorization
    {n X ℓ : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    (centralAnchorDivisor n X q).factorization ℓ =
      (if ℓ = 2 then residualPromotionCost n X else 0) +
        ∑ p ∈ largeCentralPrimes n X, (q p).factorization ℓ := by
  have hcofactorNe : largeCentralCofactorProduct n X q ≠ 0 :=
    (largeCentralCofactorProduct_pos hq).ne'
  have hqNe : ∀ p ∈ largeCentralPrimes n X, q p ≠ 0 :=
    fun p hp ↦ (largeCentralCofactor_pos hq hp).ne'
  rw [centralAnchorDivisor,
    Nat.factorization_mul
      (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hcofactorNe]
  simp only [Finsupp.add_apply, largeCentralCofactorProduct]
  rw [Nat.factorization_prod_apply hqNe]
  by_cases hℓTwo : ℓ = 2
  · subst ℓ
    rw [Nat.factorization_pow_self Nat.prime_two]
    simp
  · have htwoFactorization :
        (2 ^ residualPromotionCost n X).factorization ℓ = 0 := by
      rw [Nat.prime_two.factorization_pow]
      simp [hℓTwo]
    rw [htwoFactorization, if_neg hℓTwo, zero_add]

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.UpperScale -/
section


/-!
# Elementary scale facts for the upper bound

This module isolates the exact ceiling and endpoint used on the upper-bound
side of the paper.  Every asymptotic statement is proved directly from
elementary real-logarithm limits.  No prime-counting input is used.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section









/-- A pointwise positivity criterion for the second-order scale. -/
theorem secondOrderScale_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < secondOrderScale n := by
  rw [secondOrderScale]
  exact div_pos (by positivity)
    (Real.log_pos (by exact_mod_cast hn))

































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.UpperProductAssembly -/
section


/-!
# Exact upper-bound product assembly

This is the division-free algebra at the end of the paper.  A central anchor
set removes the central binomial coefficient together with a divisor `D` of
the tail.  A disjoint residual tail set removes the complementary tail
product.  Their union is therefore an exact complement representation, and
the complement lemma recovers a factorization of `n!`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



theorem centralTailProduct_mul_centralFactorial (n h : ℕ) :
    centralTailProduct n h * (2 * n).factorial =
      (2 * n + h).factorial := by
  exact factorInterval_prod_mul_factorial (by omega)













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorTailDivisibility -/
section


/-!
# From central-anchor valuation reserve to literal tail divisibility

The analytic part of the central-anchor argument produces inequalities at a
fixed finite set of primes.  This file supplies the exact arithmetic bridge:
the factorial-tail valuation is the valuation of the literal tail product,
and bounds on the finite support of the anchor divisor imply actual natural-
number divisibility.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- The literal tail product is positive, including when the tail is empty. -/
theorem centralTailProduct_pos (n h : ℕ) : 0 < centralTailProduct n h := by
  exact Finset.prod_pos fun a ha ↦ by
    have haMem : a ∈ Finset.Ioc (2 * n) (2 * n + h) := ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp haMem).1

/-- Exact valuation of the literal product over `(2n,2n+h]`. -/
theorem centralTailProduct_factorization (n h p : ℕ) :
    (centralTailProduct n h).factorization p =
      (2 * n + h).factorial.factorization p -
        (2 * n).factorial.factorization p := by
  have hproduct := congrArg (fun m : ℕ ↦ m.factorization p)
    (centralTailProduct_mul_centralFactorial n h)
  have htailNe : centralTailProduct n h ≠ 0 :=
    (centralTailProduct_pos n h).ne'
  have hfactorialNe : (2 * n).factorial ≠ 0 := Nat.factorial_ne_zero _
  change
    (centralTailProduct n h * (2 * n).factorial).factorization p =
      (2 * n + h).factorial.factorization p at hproduct
  rw [Nat.factorization_mul htailNe hfactorialNe] at hproduct
  simp only [Finsupp.add_apply] at hproduct
  omega

/-- The asymptotic module's tail valuation is literally the valuation of the
corresponding finite product. -/
theorem upperTailValuation_eq_centralTailProduct_factorization
    (c : ℝ) (n p : ℕ) :
    upperTailValuation c n p =
      (centralTailProduct n (upperTailLength c n)).factorization p := by
  rw [centralTailProduct_factorization]
  rfl





/-- It suffices to compare valuations on the displayed support bound. -/
theorem centralAnchorDivisor_dvd_centralTailProduct_of_support_bounds
    {n X B h : ℕ} {q : ℕ → ℕ}
    (hqChoice : IsLargeCentralCofactorChoice n X q)
    (hqBound : ∀ p ∈ largeCentralPrimes n X, q p ≤ B)
    (hvaluation : ∀ ℓ ∈ primesUpTo (max 2 B),
      (centralAnchorDivisor n X q).factorization ℓ ≤
        (centralTailProduct n h).factorization ℓ) :
    centralAnchorDivisor n X q ∣ centralTailProduct n h := by
  rw [← Nat.factorization_le_iff_dvd
    (centralAnchorDivisor_pos hqChoice).ne'
    (centralTailProduct_pos n h).ne']
  intro ℓ
  by_cases hℓPrime : ℓ.Prime
  · by_cases hℓDiv : ℓ ∣ centralAnchorDivisor n X q
    · apply hvaluation ℓ
      rw [mem_primesUpTo]
      exact ⟨hℓPrime,
        prime_dvd_centralAnchorDivisor_le hqChoice hqBound hℓPrime hℓDiv⟩
    · rw [Nat.factorization_eq_zero_of_not_dvd hℓDiv]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hℓPrime]
    exact Nat.zero_le _

/-- Specialized form in which the right-hand valuations are supplied by the
upper tail of length `ceil (c n / log n)`. -/
theorem centralAnchorDivisor_dvd_upperTail_of_support_bounds
    {c : ℝ} {n X B : ℕ} {q : ℕ → ℕ}
    (hqChoice : IsLargeCentralCofactorChoice n X q)
    (hqBound : ∀ p ∈ largeCentralPrimes n X, q p ≤ B)
    (hvaluation : ∀ ℓ ∈ primesUpTo (max 2 B),
      (centralAnchorDivisor n X q).factorization ℓ ≤
        upperTailValuation c n ℓ) :
    centralAnchorDivisor n X q ∣
      centralTailProduct n (upperTailLength c n) := by
  apply centralAnchorDivisor_dvd_centralTailProduct_of_support_bounds
    hqChoice hqBound
  intro ℓ hℓ
  rw [← upperTailValuation_eq_centralTailProduct_factorization]
  exact hvaluation ℓ hℓ



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankAnchorGuardsFinite -/
section


/-!
# Finite anchor modifications and collision guards

This module isolates the exact combinatorial part of Section 5's anchor
modification.  It chooses a replacement from three literal cofactors and
derives collision avoidance from the existing central-anchor arithmetic.
No reserve estimate or prime-distribution input appears here.
-/

namespace Erdos390.WholePaper

noncomputable section



/-- The three explicit candidates always contain a legal cofactor distinct
from both incident cores. -/
theorem prefixReplacementCofactor_spec
    {r left right : ℕ} (hr : 2 ≤ r) :
    r + 1 ≤ prefixReplacementCofactor r left right ∧
      prefixReplacementCofactor r left right ≤ 2 * r + 1 ∧
      prefixReplacementCofactor r left right ≠ left ∧
      prefixReplacementCofactor r left right ≠ right := by
  unfold prefixReplacementCofactor
  split
  next h => exact ⟨by omega, by omega, h.1, h.2⟩
  next hfirst =>
    split
    next h => exact ⟨by omega, by omega, h.1, h.2⟩
    next hsecond =>
      have hfirst' : r + 1 = left ∨ r + 1 = right := by
        by_cases hleft : r + 1 = left
        · exact Or.inl hleft
        · exact Or.inr (by
            by_contra hright
            exact hfirst ⟨hleft, hright⟩)
      have hsecond' : r + 2 = left ∨ r + 2 = right := by
        by_cases hleft : r + 2 = left
        · exact Or.inl hleft
        · exact Or.inr (by
            by_contra hright
            exact hsecond ⟨hleft, hright⟩)
      rcases hfirst' with hfirst' | hfirst' <;>
        rcases hsecond' with hsecond' | hsecond' <;> omega

















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

/-- The explicit threshold also puts `2n` strictly below the cutoff square. -/
theorem two_mul_lt_centralAnchorCutoff_sq
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    2 * n < (centralAnchorCutoff R n) ^ 2 := by
  let X := centralAnchorCutoff R n
  have hX : 4 * (R + 1) ≤ X := by
    simpa only [X] using four_mul_succ_le_centralAnchorCutoff hn
  have hXPos : 0 < X := by omega
  have hnUpper : n < (R + 1) * (X + 1) := by
    simpa only [X, centralAnchorCutoff] using
      Nat.lt_mul_div_succ n (by omega : 0 < R + 1)
  have hlinear : 2 * (R + 1) * (X + 1) ≤ X ^ 2 := by
    calc
      2 * (R + 1) * (X + 1) ≤ 2 * (R + 1) * (2 * X) := by
        exact Nat.mul_le_mul_left (2 * (R + 1)) (by omega)
      _ = (4 * (R + 1)) * X := by ring
      _ ≤ X * X := Nat.mul_le_mul_right X hX
      _ = X ^ 2 := by ring
  calc
    2 * n < 2 * ((R + 1) * (X + 1)) :=
      (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hnUpper
    _ = 2 * (R + 1) * (X + 1) := by ring
    _ ≤ X ^ 2 := hlinear



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

















/-- Direct exact-product corollary at the fixed-`R` cutoff. -/
theorem fullCentralAnchors_prod_centralAnchorCutoff
    {R n : ℕ} {q : ℕ → ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q) :
    (fullCentralAnchors n (centralAnchorCutoff R n) q).prod id =
      Nat.choose (2 * n) n *
        centralAnchorDivisor n (centralAnchorCutoff R n) q := by
  exact fullCentralAnchors_prod
    ((centralAnchorCutoffThreshold_pos R).trans_le hn)
    (two_le_centralAnchorCutoff hn)
    (two_mul_lt_centralAnchorCutoff_sq hn) hq



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorModificationAlgebra -/
section


/-!
# Valuation cost of finite central-cofactor modifications

Later bank guards change the routed cofactor at a finite, explicit set of
central marker primes.  This file records the exact valuation cost of that
operation.  It does not assume that a modification is available: both
cofactor choices, the changed marker set, and equality off that set are
literal inputs.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- A positive integer at most `B` has no more than `log_ℓ B` copies of a
prime `ℓ` in its factorization. -/
theorem factorization_le_log_of_pos_le
    {a B ℓ : ℕ} (ha : 0 < a) (haB : a ≤ B) (hℓ : ℓ.Prime) :
    a.factorization ℓ ≤ Nat.log ℓ B := by
  have hpowDvd : ℓ ^ (a.factorization ℓ) ∣ a :=
    (hℓ.pow_dvd_iff_le_factorization ha.ne').mpr le_rfl
  have hpowLe : ℓ ^ (a.factorization ℓ) ≤ a :=
    Nat.le_of_dvd ha hpowDvd
  exact (Nat.le_log_of_pow_le hℓ.one_lt hpowLe).trans
    (Nat.log_mono_right haB)

/-- Changing routed cofactors at the explicit marker set `changed` costs at
most `changed.card * log₂ B` at every prime.  The promotion power of two is
unchanged and therefore cancels from the comparison. -/
theorem centralAnchorDivisor_factorization_le_add_changed_cost
    {n X B ℓ : ℕ} {q q' : ℕ → ℕ} {changed : Finset ℕ}
    (hℓ : ℓ.Prime)
    (hq : IsLargeCentralCofactorChoice n X q)
    (hq' : IsLargeCentralCofactorChoice n X q')
    (hchanged : changed ⊆ largeCentralPrimes n X)
    (hsame : ∀ p ∈ largeCentralPrimes n X,
      p ∉ changed → q' p = q p)
    (hq'Bound : ∀ p ∈ largeCentralPrimes n X, q' p ≤ B) :
    (centralAnchorDivisor n X q').factorization ℓ ≤
      (centralAnchorDivisor n X q).factorization ℓ +
        changed.card * Nat.log 2 B := by
  classical
  let large := largeCentralPrimes n X
  have hpoint : ∀ p ∈ large,
      (q' p).factorization ℓ ≤
        (q p).factorization ℓ +
          if p ∈ changed then Nat.log 2 B else 0 := by
    intro p hp
    by_cases hpChanged : p ∈ changed
    · have hfactorization :
          (q' p).factorization ℓ ≤ Nat.log ℓ B :=
        factorization_le_log_of_pos_le
          (largeCentralCofactor_pos hq' hp) (hq'Bound p hp) hℓ
      have hlog : Nat.log ℓ B ≤ Nat.log 2 B :=
        Nat.log_anti_left Nat.one_lt_two hℓ.two_le
      simp only [hpChanged, if_pos]
      omega
    · rw [if_neg hpChanged, hsame p hp hpChanged]
      omega
  have hfilter : large.filter (fun p ↦ p ∈ changed) = changed := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun hp ↦ hp.2
    · intro hp
      exact ⟨hchanged hp, hp⟩
  have hindicator :
      ∑ p ∈ large, (if p ∈ changed then Nat.log 2 B else 0) =
        changed.card * Nat.log 2 B := by
    rw [← Finset.sum_filter, hfilter]
    simp
  have hsum :
      ∑ p ∈ large, (q' p).factorization ℓ ≤
        (∑ p ∈ large, (q p).factorization ℓ) +
          changed.card * Nat.log 2 B := by
    calc
      ∑ p ∈ large, (q' p).factorization ℓ ≤
          ∑ p ∈ large,
            ((q p).factorization ℓ +
              if p ∈ changed then Nat.log 2 B else 0) := by
        exact Finset.sum_le_sum fun p hp ↦ hpoint p hp
      _ = (∑ p ∈ large, (q p).factorization ℓ) +
          ∑ p ∈ large,
            (if p ∈ changed then Nat.log 2 B else 0) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ p ∈ large, (q p).factorization ℓ) +
          changed.card * Nat.log 2 B := by rw [hindicator]
  rw [centralAnchorDivisor_factorization hq',
    centralAnchorDivisor_factorization hq]
  simpa only [large, Nat.add_assoc] using Nat.add_le_add_left hsum _

/-- Additive reserve survives a finite modification after subtracting the
explicit modification budget. -/
theorem centralAnchorReserve_transfer_after_changed_cost
    {n X B ℓ : ℕ} {q q' : ℕ → ℕ} {changed : Finset ℕ}
    {reserve loss tail : ℝ}
    (hℓ : ℓ.Prime)
    (hq : IsLargeCentralCofactorChoice n X q)
    (hq' : IsLargeCentralCofactorChoice n X q')
    (hchanged : changed ⊆ largeCentralPrimes n X)
    (hsame : ∀ p ∈ largeCentralPrimes n X,
      p ∉ changed → q' p = q p)
    (hq'Bound : ∀ p ∈ largeCentralPrimes n X, q' p ≤ B)
    (hcost : ((changed.card * Nat.log 2 B : ℕ) : ℝ) ≤ loss)
    (hreserve : reserve +
        ((centralAnchorDivisor n X q).factorization ℓ : ℝ) ≤ tail) :
    reserve - loss +
        ((centralAnchorDivisor n X q').factorization ℓ : ℝ) ≤ tail := by
  have hvaluationNat :=
    centralAnchorDivisor_factorization_le_add_changed_cost hℓ hq hq'
      hchanged hsame hq'Bound
  have hvaluation :
      ((centralAnchorDivisor n X q').factorization ℓ : ℝ) ≤
        ((centralAnchorDivisor n X q).factorization ℓ : ℝ) +
          ((changed.card * Nat.log 2 B : ℕ) : ℝ) := by
    exact_mod_cast hvaluationNat
  linarith

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorGuardedChoice -/
section


/-!
# A concrete guarded modification of routed central cofactors

For a finite set of bank markers, row one uses the literal replacement
cofactor `3`.  Every higher positive carry row uses the first of
`r+1,r+2,r+3` which avoids the two incident bank-state cores.  This file is
pure finite arithmetic: it proves that the modified function is still an
actual routed central-cofactor choice and records the exact hypotheses under
which both incident cores are avoided.
-/

namespace Erdos390.WholePaper

noncomputable section







/-- Replacing every changed marker by the displayed row-legal cofactor
preserves the simultaneous routed-choice predicate.  The assumption
`p ≤ n` rules out the row-zero branch for a changed bank marker. -/
theorem guardedCentralCofactor_isChoice
    {R n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ}
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q)
    (hchanged : changed ⊆
      largeCentralPrimes n (centralAnchorCutoff R n))
    (hchangedLe : ∀ p ∈ changed, p ≤ n) :
    IsLargeCentralCofactorChoice n (centralAnchorCutoff R n)
      (guardedCentralCofactor n q left right changed) := by
  intro p hpLarge
  by_cases hpChanged : p ∈ changed
  · have hpLe : p ≤ n := hchangedLe p hpChanged
    have hpChangedLarge := hchanged hpChanged
    rcases hq p hpChangedLarge with hzero |
        ⟨r, hrPos, hrEq, hpRow, _hqLower, _hqUpper⟩
    · exact (not_lt_of_ge hpLe hzero.1).elim
    · subst r
      right
      refine ⟨n / p, hrPos, rfl, hpRow, ?_, ?_⟩
      by_cases hrowOne : n / p = 1
      · simp [guardedCentralCofactor, hpChanged, hrowOne]
      · have hrowTwo : 2 ≤ n / p := by omega
        simp only [guardedCentralCofactor, if_pos hpChanged,
          if_neg hrowOne]
        exact (prefixReplacementCofactor_spec hrowTwo).1
      by_cases hrowOne : n / p = 1
      · simp [guardedCentralCofactor, hpChanged, hrowOne]
      · have hrowTwo : 2 ≤ n / p := by omega
        simp only [guardedCentralCofactor, if_pos hpChanged,
          if_neg hrowOne]
        exact (prefixReplacementCofactor_spec hrowTwo).2.1
  · simpa only [guardedCentralCofactor_eq_of_not_mem hpChanged] using
      hq p hpLarge

/-- At a changed marker the guarded cofactor differs from both incident
state cores.  Row one's extra hypothesis is exactly what the literal bottom
path and the ordinary path supply; all higher rows are automatic. -/
theorem guardedCentralCofactor_ne_incidentCores
    {R n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ}
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q)
    (hchangedLe : ∀ p ∈ changed, p ≤ n)
    (hrowOneAvoid : ∀ p ∈ changed, n / p = 1 →
      3 ≠ left p ∧ 3 ≠ right p)
    {p : ℕ} (hpLarge :
      p ∈ largeCentralPrimes n (centralAnchorCutoff R n))
    (hpChanged : p ∈ changed) :
    guardedCentralCofactor n q left right changed p ≠ left p ∧
      guardedCentralCofactor n q left right changed p ≠ right p := by
  have hpLe : p ≤ n := hchangedLe p hpChanged
  rcases hq p hpLarge with hzero |
      ⟨r, hrPos, hrEq, _hpRow, _hqLower, _hqUpper⟩
  · exact (not_lt_of_ge hpLe hzero.1).elim
  · subst r
    by_cases hrowOne : n / p = 1
    · simpa [guardedCentralCofactor, hpChanged, hrowOne] using
        hrowOneAvoid p hpChanged hrowOne
    · have hrowTwo : 2 ≤ n / p := by omega
      have hspec := prefixReplacementCofactor_spec
        (r := n / p) (left := left p) (right := right p) hrowTwo
      simpa only [guardedCentralCofactor, if_pos hpChanged,
        if_neg hrowOne] using hspec.2.2

/-- The guarded function agrees with the original choice off the literal
changed set, in the exact form consumed by the valuation-cost theorem. -/
theorem guardedCentralCofactor_eq_off_changed
    {R n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ} :
    ∀ p ∈ largeCentralPrimes n (centralAnchorCutoff R n),
      p ∉ changed →
        guardedCentralCofactor n q left right changed p = q p := by
  intro p _hp hpChanged
  exact guardedCentralCofactor_eq_of_not_mem hpChanged

/-- Every guarded cofactor remains in the same fixed prefix bound. -/
theorem guardedCentralCofactor_le_fixedPrefix
    {R n : ℕ} {q left right : ℕ → ℕ} {changed : Finset ℕ}
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q)
    (hchanged : changed ⊆
      largeCentralPrimes n (centralAnchorCutoff R n))
    (hchangedLe : ∀ p ∈ changed, p ≤ n) :
    ∀ p ∈ largeCentralPrimes n (centralAnchorCutoff R n),
      guardedCentralCofactor n q left right changed p ≤ 2 * R + 1 := by
  have hchoice := guardedCentralCofactor_isChoice
    (left := left) (right := right) hq hchanged hchangedLe
  intro p hp
  exact largeCentralCofactor_le_fixedPrefix hchoice hp



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorGuardedCertificate -/
section


/-!
# Central-anchor certificate after a finite bank guard

This module packages the preceding finite modification into the same kind of
literal object used by the central-anchor existence theorem.  A sixth of the
original `c-C0` valuation margin pays for all changed cofactors; another
sixth remains visible prime by prime.  The modified divisor is then proved to
divide the actual factorial tail, rather than merely satisfying a real-valued
estimate.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section



/-- Spend at most one sixth of the original reserve on a literal finite
cofactor modification.  All support, exact-product, interval, divisibility,
and collision conclusions concern the newly constructed function itself. -/
theorem guardedCentralAnchorCertificate_of_changeCost
    {c : ℝ} {R n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (hc : C0 < c) (hR : 1 ≤ R)
    (hnCutoff : centralAnchorCutoffThreshold R ≤ n)
    (certificate : CentralAnchorCertificate c R n)
    (hchanged : changed ⊆
      largeCentralPrimes n (centralAnchorCutoff R n))
    (hchangedLe : ∀ p ∈ changed, p ≤ n)
    (hrowOneAvoid : ∀ p ∈ changed, n / p = 1 →
      3 ≠ left p ∧ 3 ≠ right p)
    (hchangeCost : ∀ ℓ ∈ primesUpTo (2 * R + 1),
      ((changed.card * Nat.log 2 (2 * R + 1) : ℕ) : ℝ) ≤
        (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
          secondOrderScale n) :
    Nonempty
      (GuardedCentralAnchorCertificate c R n left right changed) := by
  let q' : ℕ → ℕ :=
    guardedCentralCofactor n certificate.q left right changed
  have hq' : IsLargeCentralCofactorChoice n
      (centralAnchorCutoff R n) q' := by
    simpa only [q'] using guardedCentralCofactor_isChoice
      certificate.isCofactorChoice hchanged hchangedLe
  have hq'Bound : ∀ p ∈
      largeCentralPrimes n (centralAnchorCutoff R n),
      q' p ≤ 2 * R + 1 := by
    simpa only [q'] using guardedCentralCofactor_le_fixedPrefix
      certificate.isCofactorChoice hchanged hchangedLe
  have hsame : ∀ p ∈
      largeCentralPrimes n (centralAnchorCutoff R n),
      p ∉ changed → q' p = certificate.q p := by
    simpa only [q'] using
      (guardedCentralCofactor_eq_off_changed
        (R := R) (n := n) (q := certificate.q)
        (left := left) (right := right) (changed := changed))
  have hmax : max 2 (2 * R + 1) = 2 * R + 1 := by omega
  have hreserve : ∀ ℓ ∈ primesUpTo (2 * R + 1),
      (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
            secondOrderScale n +
          ((centralAnchorDivisor n
            (centralAnchorCutoff R n) q').factorization ℓ : ℝ) ≤
        (upperTailValuation c n ℓ : ℝ) := by
    intro ℓ hℓ
    have hℓPrime := (mem_primesUpTo.mp hℓ).1
    have htransfer :=
      centralAnchorReserve_transfer_after_changed_cost
        (n := n) (X := centralAnchorCutoff R n)
        (B := 2 * R + 1) (ℓ := ℓ)
        (q := certificate.q) (q' := q') (changed := changed)
        (reserve :=
          (c - C0) / (3 * (((ℓ - 1 : ℕ) : ℝ))) *
            secondOrderScale n)
        (loss :=
          (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
            secondOrderScale n)
        (tail := (upperTailValuation c n ℓ : ℝ))
        hℓPrime certificate.isCofactorChoice hq' hchanged hsame
        hq'Bound (hchangeCost ℓ hℓ) (certificate.divisor_reserve ℓ hℓ)
    calc
      (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
              secondOrderScale n +
            ((centralAnchorDivisor n
              (centralAnchorCutoff R n) q').factorization ℓ : ℝ) =
          ((c - C0) / (3 * (((ℓ - 1 : ℕ) : ℝ))) *
              secondOrderScale n -
            (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
              secondOrderScale n) +
            ((centralAnchorDivisor n
              (centralAnchorCutoff R n) q').factorization ℓ : ℝ) := by
                congr 1
                ring
      _ ≤ (upperTailValuation c n ℓ : ℝ) := htransfer
  have hsupport : ∀ ℓ : ℕ, ℓ.Prime →
      ℓ ∣ centralAnchorDivisor n (centralAnchorCutoff R n) q' →
        ℓ ∈ primesUpTo (2 * R + 1) := by
    intro ℓ hℓPrime hℓDivisor
    rw [mem_primesUpTo]
    refine ⟨hℓPrime, ?_⟩
    have hbound := prime_dvd_centralAnchorDivisor_le hq' hq'Bound
      hℓPrime hℓDivisor
    simpa only [hmax] using hbound
  have hdivisor :
      centralAnchorDivisor n (centralAnchorCutoff R n) q' ∣
        centralTailProduct n (upperTailLength c n) := by
    apply centralAnchorDivisor_dvd_upperTail_of_support_bounds hq' hq'Bound
    intro ℓ hℓ
    have hℓPrefix : ℓ ∈ primesUpTo (2 * R + 1) := by
      simpa only [hmax] using hℓ
    have hres := hreserve ℓ hℓPrefix
    have hdenPos : 0 < (((ℓ - 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.sub_pos_of_lt
        (mem_primesUpTo.mp hℓPrefix).1.one_lt
    have hmarginNonneg :
        0 ≤ (c - C0) /
            (6 * (((ℓ - 1 : ℕ) : ℝ))) * secondOrderScale n := by
      have hnTwo : 2 ≤ n := by
        have hthresholdTwo : 2 ≤ centralAnchorCutoffThreshold R := by
          rw [centralAnchorCutoffThreshold]
          have hsq : 1 ≤ (R + 1) ^ 2 :=
            one_le_pow₀ (by omega : 1 ≤ R + 1)
          calc
            2 ≤ 4 := by omega
            _ = 4 * 1 := by norm_num
            _ ≤ 4 * (R + 1) ^ 2 := Nat.mul_le_mul_left 4 hsq
        exact hthresholdTwo.trans hnCutoff
      exact mul_nonneg
        (div_nonneg (sub_nonneg.mpr hc.le)
          (mul_nonneg (by norm_num) hdenPos.le))
        (secondOrderScale_pos hnTwo).le
    have hvaluationReal :
        ((centralAnchorDivisor n
          (centralAnchorCutoff R n) q').factorization ℓ : ℝ) ≤
          (upperTailValuation c n ℓ : ℝ) := by linarith
    exact_mod_cast hvaluationReal
  let anchors' : Finset ℕ :=
    fullCentralAnchors n (centralAnchorCutoff R n) q'
  refine ⟨{
    q := q'
    anchors := anchors'
    isCofactorChoice := hq'
    anchors_eq := rfl
    anchors_subset := ?_
    anchors_prod := ?_
    divisor_prime_support := hsupport
    divisor_reserve := hreserve
    divisor_dvd_tail := hdivisor
    guarded_incident_cores := ?_
  }⟩
  · have hnPos : 0 < n :=
      (centralAnchorCutoffThreshold_pos R).trans_le hnCutoff
    simpa only [anchors'] using
      fullCentralAnchors_subset_centralInterval hnPos hq'
  · simpa only [anchors'] using
      fullCentralAnchors_prod_centralAnchorCutoff hnCutoff hq'
  · intro p hpChanged
    have hpLarge := hchanged hpChanged
    simpa only [q'] using
      guardedCentralCofactor_ne_incidentCores
        certificate.isCofactorChoice hchangedLe hrowOneAvoid
          hpLarge hpChanged

end

end Erdos390.WholePaper

end

theorem solution :
∀ {c : Real} {R n : Nat} {left right : Nat → Nat} {changed : Finset.{0} Nat},
  LT.lt.{0} Erdos390.WholePaper.C0 c →
    LE.le.{0} (1 : Nat) R →
      LE.le.{0} (Erdos390.WholePaper.centralAnchorCutoffThreshold R) n →
        ∀ (certificate : Erdos390.WholePaper.CentralAnchorCertificate c R n),
          HasSubset.Subset.{0} changed
              (Erdos390.WholePaper.largeCentralPrimes n (Erdos390.WholePaper.centralAnchorCutoff R n)) →
            (∀ (p : Nat), Membership.mem.{0, 0} changed p → LE.le.{0} p n) →
              (∀ (p : Nat),
                  Membership.mem.{0, 0} changed p →
                    Eq.{1} (HDiv.hDiv.{0, 0, 0} n p) (1 : Nat) →
                      And (Ne.{1} (3 : Nat) (left p)) (Ne.{1} (3 : Nat) (right p))) →
                (∀ (ℓ : Nat),
                    Membership.mem.{0, 0}
                        (Erdos390.WholePaper.primesUpTo
                          (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) R) (1 : Nat)))
                        ℓ →
                      LE.le.{0}
                        (↑(HMul.hMul.{0, 0, 0} (Finset.card.{0} changed)
                            (Nat.log (2 : Nat) (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) R) (1 : Nat)))))
                        (HMul.hMul.{0, 0, 0}
                          (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} c Erdos390.WholePaper.C0)
                            (HMul.hMul.{0, 0, 0} (6 : Real) ↑(HSub.hSub.{0, 0, 0} ℓ (1 : Nat))))
                          (Erdos390.WholePaper.secondOrderScale n))) →
                  Nonempty.{1} (Erdos390.WholePaper.GuardedCentralAnchorCertificate c R n left right changed) := by
  exact @Erdos390.WholePaper.guardedCentralAnchorCertificate_of_changeCost
