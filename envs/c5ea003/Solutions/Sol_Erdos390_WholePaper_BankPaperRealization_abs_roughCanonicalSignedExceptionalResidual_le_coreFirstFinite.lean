-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.abs_roughCanonicalSignedExceptionalResidual_le_coreFirstFinite
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:13:13.281233+00:00
-- url     : https://prove2.me/submissions/621ec563-946b-4ccb-96e9-8731e8e4d4f7

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
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009

/- Source module: Erdos390.Full.ArithmeticModel -/
section


/-!
# Arithmetic model for the full Erdős 390 formalization

This file connects the abstract covariance columns used by the earlier audit
companion to the actual arithmetic objects in the paper.  All definitions are
total, including at `n = 0`, `m = 0`, and at non-prime bases.  The valuation
identities themselves are stated with the mathematically necessary hypotheses
that the base is prime and the sampled integer is positive.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticModel







































































/-- A prime valuation is the finite sum of its positive-power divisibility
indicators.  The common exponent cutoff may be any `M` above the sampled
integer, hence in particular a fixed physical upper bound for a whole cell. -/
theorem valuation_eq_sum_divInd_of_le {p m M : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    valuation p m = ∑ k ∈ positiveExponents M, divInd (p ^ k) m := by
  have hMpow : m ≤ p ^ M := by
    exact hmM.trans (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt))
  have hfilter := Nat.Ico_filter_pow_dvd_eq hp hm.ne' hMpow
  have hcard := Nat.factorization_eq_card_pow_dvd m hp
  calc
    valuation p m = (m.factorization p : ℝ) := rfl
    _ = (((Finset.Ico 1 m).filter fun k => p ^ k ∣ m).card : ℝ) := by
      exact_mod_cast hcard
    _ = (((Finset.Icc 1 M).filter fun k => p ^ k ∣ m).card : ℝ) := by
      rw [hfilter]
    _ = ∑ k ∈ positiveExponents M, divInd (p ^ k) m := by
      simp [positiveExponents, divInd]































end Erdos390.Full.ArithmeticModel

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











theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

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

private theorem sub_injective_on_Icc (k A : ℕ) :
    Set.InjOn (fun a : ℕ ↦ a - k) (↑(Finset.Icc k A) : Set ℕ) := by
  intro a ha b hb hab
  have hka : k ≤ a := (Finset.mem_Icc.mp ha).1
  have hkb : k ≤ b := (Finset.mem_Icc.mp hb).1
  change a - k = b - k at hab
  calc
    a = (a - k) + k := (Nat.sub_add_cancel hka).symm
    _ = (b - k) + k := congrArg (fun z : ℕ ↦ z + k) hab
    _ = b := Nat.sub_add_cancel hkb

/-- Every finite shifted half-geometric tail is bounded by the complete
geometric series. -/
theorem sum_shifted_half_le_two (k A : ℕ) :
    (∑ a ∈ Finset.Icc k A,
        (1 / (2 : ℝ)) ^ (a - k)) ≤ 2 := by
  let s := Finset.Icc k A
  let g : ℕ → ℕ := fun a ↦ a - k
  have hinj : Set.InjOn g (↑s : Set ℕ) := by
    simpa only [s, g] using sub_injective_on_Icc k A
  have heq :
      (∑ a ∈ s, (1 / (2 : ℝ)) ^ (a - k)) =
        ∑ i ∈ s.image g, (1 / (2 : ℝ)) ^ i := by
    symm
    rw [Finset.sum_image]
    exact hinj
  rw [heq]
  exact (summable_geometric_two.sum_le_tsum (s.image g)
    (fun i hi ↦ by positivity)).trans_eq tsum_geometric_two









/-- A finite reciprocal-power tail beginning at exponent `r+1` has the
same bound as the corresponding infinite geometric tail. -/
theorem sum_inv_pow_tail_le {p r A : ℕ} (hp : 2 ≤ p) :
    (∑ a ∈ Finset.Icc (r + 1) A,
        1 / ((p ^ a : ℕ) : ℝ)) ≤
      2 / (p : ℝ) ^ (r + 1) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpPos : (0 : ℝ) < (p : ℝ) := by positivity
  calc
    (∑ a ∈ Finset.Icc (r + 1) A,
        1 / ((p ^ a : ℕ) : ℝ)) ≤
      ∑ a ∈ Finset.Icc (r + 1) A,
        (1 / (p : ℝ) ^ (r + 1)) *
          (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
      apply Finset.sum_le_sum
      intro a ha
      have hra : r + 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have hpPow : (2 : ℝ) ^ (a - (r + 1)) ≤
          (p : ℝ) ^ (a - (r + 1)) := by gcongr
      have haSplit : a = (r + 1) + (a - (r + 1)) := by omega
      have hpowSplit : (p : ℝ) ^ a =
          (p : ℝ) ^ (r + 1) * (p : ℝ) ^ (a - (r + 1)) := by
        conv_lhs => rw [haSplit]
        rw [pow_add]
      norm_num only [Nat.cast_pow]
      rw [hpowSplit]
      calc
        1 / ((p : ℝ) ^ (r + 1) * (p : ℝ) ^ (a - (r + 1))) ≤
            1 / ((p : ℝ) ^ (r + 1) *
              (2 : ℝ) ^ (a - (r + 1))) := by
          gcongr
        _ = (1 / (p : ℝ) ^ (r + 1)) *
            (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ) ^ (r + 1)) *
        ∑ a ∈ Finset.Icc (r + 1) A,
          (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (p : ℝ) ^ (r + 1)) * 2 :=
      mul_le_mul_of_nonneg_left (sum_shifted_half_le_two (r + 1) A)
        (by positivity)
    _ = 2 / (p : ℝ) ^ (r + 1) := by ring





























end

end Erdos390.Full.LocalFugacityBounds

end

/- Source module: Erdos390.WholePaper.RoughHeadCompatibleFinitePoint -/
section


/-!
# The literal head-compatible finite raw point

This file constructs the first finite point in the guarded rough selector.
The upper block `E`, the high lower block `H`, and the broad lower block `J`
are literal natural-number half-open intervals.  Head freedom is imposed by
coprimality with the product of all primes up to `W`, and the raw weight is
defined pointwise from those finite sets.

The second half proves the exact deterministic identities used before any
HT--Saias or prime-number estimate: finite Möbius inclusion--exclusion,
reindexing of smooth multiples by division, and the resulting physical-block
shift through every divisor of the head modulus.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Literal physical intervals -/





















/-! ## The finite head and raw weights -/









/-- The head modulus is always positive, including for an empty head. -/
theorem roughHeadModulus_pos (W : ℕ) :
    0 < roughHeadModulus W := by
  rw [← roughHeadZeroPattern_modulus]
  exact Nat.pos_of_ne_zero (roughHeadZeroPattern W).modulus_ne_zero



/-- The complete zero-head stratum has strictly positive density. -/
theorem roughHeadDensity_pos (W : ℕ) :
    0 < roughHeadDensity W := by
  have hmod : (0 : ℝ) < (roughHeadModulus W : ℝ) := by
    exact_mod_cast roughHeadModulus_pos W
  have htot : (0 : ℝ) < ((roughHeadModulus W).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (roughHeadModulus_pos W)
  exact div_pos htot hmod



































/-! ## Exact head inclusion--exclusion and smooth physical shifts -/

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.FixedModulusReducedResidueCount -/
section


/-!
# Fixed-modulus reduced-residue counts

This file proves the elementary `O_W(1)` input used in the rough selector
and in the tangent-list census.  A reduced-residue predicate is counted on
literal finite intervals by splitting the interval into complete periods
and one remainder.  Multiples of a number coprime to the fixed modulus are
then reindexed exactly by division.

There is no prime-number theorem, smooth-number estimate, or asymptotic
hypothesis in this module.  The final CRT-style error constant is the
explicit number `M + 1`, independent of the multiplier and the interval.
-/

namespace Erdos390.WholePaper

noncomputable section









/-! ## Exact periodic decomposition -/

/-- Splitting a segment after `first` tokens splits the finite set itself. -/
theorem reducedResidueSegment_add
    (M start first second : ℕ) :
    reducedResidueSegment M start (first + second) =
      reducedResidueSegment M start first ∪
        reducedResidueSegment M (start + first) second := by
  ext a
  simp only [reducedResidueSegment, Finset.mem_filter,
    Finset.mem_Ico, Finset.mem_union]
  omega

/-- The two pieces in `reducedResidueSegment_add` are disjoint. -/
theorem reducedResidueSegment_disjoint
    (M start first second : ℕ) :
    Disjoint (reducedResidueSegment M start first)
      (reducedResidueSegment M (start + first) second) := by
  rw [Finset.disjoint_left]
  intro a haFirst haSecond
  simp only [reducedResidueSegment, Finset.mem_filter,
    Finset.mem_Ico] at haFirst haSecond
  omega

/-- Cardinalities add under the literal segment split. -/
theorem reducedResidueSegment_card_add
    (M start first second : ℕ) :
    (reducedResidueSegment M start (first + second)).card =
      (reducedResidueSegment M start first).card +
        (reducedResidueSegment M (start + first) second).card := by
  rw [reducedResidueSegment_add,
    Finset.card_union_of_disjoint
      (reducedResidueSegment_disjoint M start first second)]

/-- Every complete interval of length `M` contains exactly `phi(M)`
reduced residues, regardless of its starting point. -/
theorem reducedResidueSegment_card_period
    (M start : ℕ) :
    (reducedResidueSegment M start M).card = M.totient := by
  simpa only [reducedResidueSegment, Nat.coprime_comm] using
    Nat.filter_coprime_Ico_eq_totient M start

/-- `q` complete periods contain exactly `q * phi(M)` reduced residues. -/
theorem reducedResidueSegment_card_fullBlocks
    (M start q : ℕ) :
    (reducedResidueSegment M start (q * M)).card =
      q * M.totient := by
  induction q generalizing start with
  | zero => simp [reducedResidueSegment]
  | succ q ih =>
      calc
        (reducedResidueSegment M start ((q + 1) * M)).card =
            (reducedResidueSegment M start (q * M)).card +
              (reducedResidueSegment M (start + q * M) M).card := by
          rw [Nat.succ_mul, reducedResidueSegment_card_add]
        _ = q * M.totient + M.totient := by
          rw [ih, reducedResidueSegment_card_period]
        _ = (q + 1) * M.totient := by ring

/-- Exact quotient-and-remainder formula for every finite segment. -/
theorem reducedResidueSegment_card_eq_fullBlocks_add_remainder
    (M start length : ℕ) :
    (reducedResidueSegment M start length).card =
      (length / M) * M.totient +
        (reducedResidueSegment M
          (start + (length / M) * M) (length % M)).card := by
  have hlength :
      length = (length / M) * M + length % M := by
    calc
      length = length % M + M * (length / M) :=
        (Nat.mod_add_div length M).symm
      _ = (length / M) * M + length % M := by ac_rfl
  calc
    (reducedResidueSegment M start length).card =
        (reducedResidueSegment M start
          ((length / M) * M + length % M)).card :=
      congrArg (fun segmentLength ↦
        (reducedResidueSegment M start segmentLength).card) hlength
    _ = (reducedResidueSegment M start ((length / M) * M)).card +
        (reducedResidueSegment M
          (start + (length / M) * M) (length % M)).card :=
      reducedResidueSegment_card_add M start
        ((length / M) * M) (length % M)
    _ = (length / M) * M.totient +
        (reducedResidueSegment M
          (start + (length / M) * M) (length % M)).card := by
      rw [reducedResidueSegment_card_fullBlocks]

/-- A filtered segment contains at most its literal number of tokens. -/
theorem reducedResidueSegment_card_le_length
    (M start length : ℕ) :
    (reducedResidueSegment M start length).card ≤ length := by
  unfold reducedResidueSegment
  calc
    ((Finset.Ico start (start + length)).filter
        (fun a ↦ Nat.Coprime a M)).card ≤
      (Finset.Ico start (start + length)).card :=
        Finset.card_filter_le _ _
    _ = length := by simp

/-- A physical `(lo,hi]` interval is literally the corresponding shifted
half-open segment. -/
theorem reducedResidueIoc_eq_segment
    {M lo hi : ℕ} (hlohi : lo ≤ hi) :
    reducedResidueIoc M lo hi =
      reducedResidueSegment M (lo + 1) (hi - lo) := by
  ext a
  simp only [reducedResidueIoc, reducedResidueSegment,
    Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
  omega

/-! ## Explicit fixed-period error -/

/-- The exact endpoint error is bounded by the length of the incomplete
period, not merely by an unspecified modulus-dependent constant. -/
theorem reducedResidueSegment_card_error_le_mod
    {M : ℕ} (hM : 0 < M) (start length : ℕ) :
    |((reducedResidueSegment M start length).card : ℝ) -
        fixedModulusReducedResidueDensity M * (length : ℝ)| ≤
      ((length % M : ℕ) : ℝ) := by
  let q := length / M
  let r := length % M
  let remainderCard :=
    (reducedResidueSegment M (start + q * M) r).card
  have hcount :
      (reducedResidueSegment M start length).card =
        q * M.totient + remainderCard := by
    simpa only [q, r, remainderCard] using
      reducedResidueSegment_card_eq_fullBlocks_add_remainder
        M start length
  have hlength : length = q * M + r := by
    dsimp only [q, r]
    calc
      length = length % M + M * (length / M) :=
        (Nat.mod_add_div length M).symm
      _ = (length / M) * M + length % M := by ac_rfl
  have hremainderLeNat : remainderCard ≤ r := by
    dsimp only [remainderCard]
    exact reducedResidueSegment_card_le_length M (start + q * M) r
  have hremainderLe : (remainderCard : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast hremainderLeNat
  have hMRealPos : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast hM
  have hMReal : (M : ℝ) ≠ 0 := hMRealPos.ne'
  have htotientLe : (M.totient : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast Nat.totient_le M
  have hdensityNonneg :
      0 ≤ fixedModulusReducedResidueDensity M := by
    exact div_nonneg (Nat.cast_nonneg _) hMRealPos.le
  have hdensityLeOne :
      fixedModulusReducedResidueDensity M ≤ 1 := by
    rw [fixedModulusReducedResidueDensity]
    exact (div_le_one hMRealPos).2 htotientLe
  have hmainNonneg :
      0 ≤ fixedModulusReducedResidueDensity M * (r : ℝ) :=
    mul_nonneg hdensityNonneg (Nat.cast_nonneg _)
  have hmainLe :
      fixedModulusReducedResidueDensity M * (r : ℝ) ≤ (r : ℝ) := by
    calc
      fixedModulusReducedResidueDensity M * (r : ℝ) ≤
          1 * (r : ℝ) :=
        mul_le_mul_of_nonneg_right hdensityLeOne (Nat.cast_nonneg _)
      _ = (r : ℝ) := one_mul _
  have herror :
      ((reducedResidueSegment M start length).card : ℝ) -
          fixedModulusReducedResidueDensity M * (length : ℝ) =
        (remainderCard : ℝ) -
          fixedModulusReducedResidueDensity M * (r : ℝ) := by
    rw [hcount, hlength]
    simp only [fixedModulusReducedResidueDensity, Nat.cast_add,
      Nat.cast_mul]
    field_simp [hMReal]
    ring
  have hremainderNonneg : (0 : ℝ) ≤ (remainderCard : ℝ) := by
    exact Nat.cast_nonneg remainderCard
  rw [herror, abs_le]
  constructor <;> linarith

/-- Physical-interval form of the exact remainder bound. -/
theorem reducedResidueIoc_card_error_le_mod
    {M lo hi : ℕ} (hM : 0 < M) (hlohi : lo ≤ hi) :
    |((reducedResidueIoc M lo hi).card : ℝ) -
        fixedModulusReducedResidueDensity M * ((hi - lo : ℕ) : ℝ)| ≤
      (((hi - lo) % M : ℕ) : ℝ) := by
  rw [reducedResidueIoc_eq_segment hlohi]
  exact reducedResidueSegment_card_error_le_mod hM (lo + 1) (hi - lo)

/-- Coarser but convenient `O_M(1)` form with the explicit constant `M`. -/
theorem reducedResidueIoc_card_error_le_modulus
    {M lo hi : ℕ} (hM : 0 < M) (hlohi : lo ≤ hi) :
    |((reducedResidueIoc M lo hi).card : ℝ) -
        fixedModulusReducedResidueDensity M * ((hi - lo : ℕ) : ℝ)| ≤
      (M : ℝ) := by
  exact (reducedResidueIoc_card_error_le_mod hM hlohi).trans
    (by exact_mod_cast (Nat.mod_lt (hi - lo) hM).le)

/-! ## Exact CRT reindexing and multiplier-independent error -/







/-! ## Paper-head specializations -/

/-- The fixed-head reduced-residue count with explicit error
`roughHeadModulus W`. -/
theorem roughHeadFree_Ioc_card_error_le
    {W lo hi : ℕ} (hlohi : lo ≤ hi) :
    |((roughHeadFree W (Finset.Ioc lo hi)).card : ℝ) -
        roughHeadDensity W * ((hi - lo : ℕ) : ℝ)| ≤
      (roughHeadModulus W : ℝ) := by
  simpa only [roughHeadFree, reducedResidueIoc,
    roughHeadDensity, fixedModulusReducedResidueDensity] using
    reducedResidueIoc_card_error_le_modulus
      (roughHeadModulus_pos W) hlohi



/-- A prime strictly above the cutoff is coprime to the product of every
head prime at or below the cutoff. -/
theorem prime_coprime_roughHeadModulus_of_cutoff_lt
    {W p : ℕ} (hp : p.Prime) (hWp : W < p) :
    Nat.Coprime p (roughHeadModulus W) := by
  rw [roughHeadModulus, Nat.coprime_prod_right_iff]
  intro q hq
  have hqData := mem_primesUpTo.mp hq
  exact (Nat.coprime_primes hp hqData.1).mpr (by omega)



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







/-- For a positive original number, the complementary quotient is positive. -/
theorem completeSmoothPart_pos {y a : ℕ} (ha : 0 < a) :
    0 < completeSmoothPart y a := by
  rw [completeSmoothPart]
  apply Nat.div_pos
  · exact Nat.le_of_dvd ha (completeRoughLabel_dvd y a)
  · exact completeRoughLabel_pos y a



/-! ## Uniqueness and the smooth-label criterion -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalBacking -/
section


/-!
# The literal fixed exceptional factors and their high-prime backing

The paper fixes every upper-tail factor whose complete rough row has real
scale `2n / R_y(a) < n ^ deltaStar`, except for the actual donor occurrences
already withheld for the precharged bank.  This file makes that set literal.

The definition deliberately uses the displayed real quotient and real power.
It is not the larger integral test obtained by flooring the rough scale and
ceiling the exceptional cutoff.

At every prime above the rough cutoff, replacing the donor set by the bank's
base state preserves factorization coordinatewise.  The fixed exceptional
factors and donors are disjoint subsets of the literal tail, so their union
is an unconditional backing product for the complete selector charge in
all such coordinates.  No small-prime charge estimate is asserted here.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section





theorem paperExceptionalUpperFactors_subset_upperBlock
    (n h : ℕ) (deltaStar : ℝ) :
    paperExceptionalUpperFactors n h deltaStar ⊆
      roughUpperBlock n h :=
  Finset.filter_subset _ _

namespace BankPaperRealization



























end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalValuationFibers -/
section


/-!
# Finite valuation fibres for the literal fixed exceptional factors

This file gives the first finite low-prime bridge for the paper's literal
fixed exceptional set.  The exceptional upper factors are partitioned by
their complete smooth part at the canonical cutoff `yNat n`.  At a prime
`p ≤ yNat n`, the factorization charge is therefore the corresponding
smooth-part valuation times the size of each fibre.

Each actual fibre injects, by its complete rough label, into the physical
reduced-residue interval obtained by dividing `(2n,2n+h]` by that smooth
part.  The last theorem substitutes the already proved canonical finite
Selberg estimate for these candidate intervals.  No smooth-number census,
valuation-sum estimate, or asymptotic exceptional-charge bound is asserted
here.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Canonical smooth fibres and their rough candidates -/













/-- Every literal exceptional upper factor is positive. -/
theorem paperExceptionalUpperFactors_pos
    {n h a : ℕ} {deltaStar : ℝ}
    (ha : a ∈ paperExceptionalUpperFactors n h deltaStar) :
    0 < a := by
  have haInterval : a ∈ Finset.Ioc (2 * n) (2 * n + h) := by
    simpa only [roughUpperBlock] using
      (paperExceptionalUpperFactors_subset_upperBlock n h deltaStar ha)
  exact lt_of_le_of_lt (Nat.zero_le (2 * n))
    (Finset.mem_Ioc.mp haInterval).1

/-! ## Exact low-prime valuation partition -/

/-- At a low prime, the full literal exceptional product has exactly the
smooth-part weighted fibre decomposition. -/
theorem paperExceptionalUpperFactors_prod_factorization_eq_smoothFiberSum
    {n h p : ℕ} {deltaStar : ℝ} (hp : p ≤ yNat n) :
    ((paperExceptionalUpperFactors n h deltaStar).prod id).factorization p =
      ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
        b.factorization p *
          (paperExceptionalSmoothFiber n h deltaStar b).card := by
  have hfactorization :
      ((paperExceptionalUpperFactors n h deltaStar).prod id).factorization p =
        ∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
          a.factorization p :=
    Nat.factorization_prod_apply
      (fun a ha ↦ (paperExceptionalUpperFactors_pos ha).ne')
  rw [hfactorization]
  calc
    (∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
        a.factorization p) =
        ∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
          (completeSmoothPart (yNat n) a).factorization p := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [completeSmoothPart_factorization_apply, if_pos hp]
    _ = ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
          ∑ a ∈ paperExceptionalSmoothFiber n h deltaStar b,
            (completeSmoothPart (yNat n) a).factorization p := by
      symm
      simpa only [paperExceptionalSmoothParts,
        paperExceptionalSmoothFiber] using
        (Finset.sum_fiberwise_of_maps_to
          (s := paperExceptionalUpperFactors n h deltaStar)
          (t := (paperExceptionalUpperFactors n h deltaStar).image
            (completeSmoothPart (yNat n)))
          (g := completeSmoothPart (yNat n))
          (fun a ha ↦ Finset.mem_image_of_mem
            (completeSmoothPart (yNat n)) ha)
          (fun a ↦ (completeSmoothPart (yNat n) a).factorization p))
    _ = ∑ b ∈ paperExceptionalSmoothParts n h deltaStar,
          b.factorization p *
            (paperExceptionalSmoothFiber n h deltaStar b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      calc
        (∑ a ∈ paperExceptionalSmoothFiber n h deltaStar b,
            (completeSmoothPart (yNat n) a).factorization p) =
            (paperExceptionalSmoothFiber n h deltaStar b).card *
              b.factorization p := by
          apply Finset.sum_const_nat
          intro a ha
          rw [(mem_paperExceptionalSmoothFiber.mp ha).2]
        _ = b.factorization p *
              (paperExceptionalSmoothFiber n h deltaStar b).card :=
          Nat.mul_comm _ _

/-! ## Injection of each actual fibre into a reduced-residue interval -/







/-! ## The fixed exceptional product -/

namespace BankPaperRealization





end BankPaperRealization

/-! ## Canonical Selberg substitution on each candidate interval -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.ExceptionalValuationSums -/
section


/-!
# Elementary finite valuation sums

This file records the two elementary estimates used when a fixed exceptional
integer contributes a factorization-coordinate charge (the `p`-adic charge
when `p` is prime).  The unweighted prefix is exactly the corresponding
factorization coordinate of a factorial.  Discrete summation by parts then
converts the same prefix estimate into a harmonic weighted bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The total factorization coordinate of the positive integers at most `B`
is the same coordinate of `B!`.  For prime `p`, this is the usual `p`-adic
valuation identity; primality is not needed for the factorization identity. -/
theorem sum_factorization_Icc_eq_factorialFactorization (p B : ℕ) :
    (∑ b ∈ Finset.Icc 1 B, b.factorization p) =
      B.factorial.factorization p := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [← Finset.prod_Ico_id_eq_factorial]
  exact (Nat.factorization_prod_apply fun b hb ↦
    (Nat.ne_of_gt (Finset.mem_Ico.mp hb).1)).symm

/-- Natural-valued Legendre bound for the total valuation of
`1, ..., B`. -/
theorem sum_factorization_Icc_le_div_pred {p B : ℕ} (hp : p.Prime) :
    (∑ b ∈ Finset.Icc 1 B, b.factorization p) ≤ B / (p - 1) := by
  rw [sum_factorization_Icc_eq_factorialFactorization]
  exact Nat.factorization_factorial_le_div_pred hp B

/-- Real version of the elementary Legendre prefix bound. -/
theorem sum_factorization_Icc_cast_le_div_pred {p B : ℕ} (hp : p.Prime) :
    (∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)) ≤
      (B : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  calc
    (∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)) =
        ((∑ b ∈ Finset.Icc 1 B, b.factorization p : ℕ) : ℝ) := by
      simp only [Nat.cast_sum]
    _ ≤ ((B / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast sum_factorization_Icc_le_div_pred hp
    _ ≤ (B : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le







theorem valuationPrefixReal_le_div_pred {p B : ℕ} (hp : p.Prime) :
    valuationPrefixReal p B ≤
      (B : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  simpa only [valuationPrefixReal] using
    sum_factorization_Icc_cast_le_div_pred (p := p) (B := B) hp

/-- A range beginning at zero is the positive valuation prefix because the
factorization of zero is defined to be zero. -/
theorem sum_range_succ_factorization_cast_eq_valuationPrefixReal (p B : ℕ) :
    (∑ b ∈ Finset.range (B + 1), (b.factorization p : ℝ)) =
      valuationPrefixReal p B := by
  rw [Nat.range_eq_Icc_zero_sub_one _ (Nat.add_one_ne_zero B),
    Nat.add_sub_cancel_right]
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le B), Finset.sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc]
  simp [valuationPrefixReal]

/-- Exact finite Abel identity for the harmonically weighted valuation sum. -/
theorem weightedFactorizationSum_eq_abel {p B : ℕ} (hB : 1 ≤ B) :
    (∑ b ∈ Finset.Icc 1 B,
        (1 / (b : ℝ)) * (b.factorization p : ℝ)) =
      (1 / (B : ℝ)) * valuationPrefixReal p B +
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
            valuationPrefixReal p b := by
  have hBpos : 0 < B := by omega
  have habel := Finset.sum_Ioc_by_parts
    (f := fun b : ℕ ↦ 1 / (b : ℝ))
    (g := fun b : ℕ ↦ (b.factorization p : ℝ))
    (m := 0) (n := B) hBpos
  have hIoc : Finset.Ioc 0 B = Finset.Icc 1 B := by
    simpa only [zero_add] using
      (Finset.Icc_add_one_left_eq_Ioc 0 B).symm
  rw [hIoc] at habel
  simp_rw [sum_range_succ_factorization_cast_eq_valuationPrefixReal] at habel
  simp only [smul_eq_mul, zero_add, Nat.cast_one, div_one,
    valuationPrefixReal_zero, mul_zero, sub_zero] at habel
  have hneg :
      -(∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / ((b + 1 : ℕ) : ℝ) - 1 / (b : ℝ)) *
            valuationPrefixReal p b) =
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
            valuationPrefixReal p b := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  calc
    (∑ b ∈ Finset.Icc 1 B,
        (1 / (b : ℝ)) * (b.factorization p : ℝ)) =
        (1 / (B : ℝ)) * valuationPrefixReal p B -
          ∑ b ∈ Finset.Ioc 0 (B - 1),
            (1 / ((b + 1 : ℕ) : ℝ) - 1 / (b : ℝ)) *
              valuationPrefixReal p b := habel
    _ = _ := by rw [sub_eq_add_neg, hneg]

private theorem one_add_sum_Ioc_succ_reciprocal_eq_harmonic
    {B : ℕ} (hB : 1 ≤ B) :
    1 + ∑ b ∈ Finset.Ioc 0 (B - 1),
        1 / ((b + 1 : ℕ) : ℝ) = (harmonic B : ℝ) := by
  have hset : Finset.Ioc 0 (B - 1) = Finset.Ico 1 B := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, Nat.sub_add_cancel hB]
    simp
  have hshift :
      (∑ b ∈ Finset.Ico 1 B, 1 / ((b + 1 : ℕ) : ℝ)) =
        ∑ k ∈ Finset.Ico 2 (B + 1), 1 / (k : ℝ) := by
    simpa only [one_add_one_eq_two] using
      (Finset.sum_Ico_add' (fun k : ℕ ↦ 1 / (k : ℝ)) 1 B 1)
  rw [hset, hshift, Finset.Ico_add_one_right_eq_Icc]
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [Finset.Icc_eq_cons_Ioc hB, Finset.sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc]
  norm_num

/-- Sharp elementary harmonic bound for the weighted valuation sum. -/
theorem weightedFactorizationSum_le_one_add_log_div_pred
    {p B : ℕ} (hp : p.Prime) (hB : 1 ≤ B) :
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : ℝ) / (b : ℝ)) ≤
      (1 + Real.log (B : ℝ)) / ((p - 1 : ℕ) : ℝ) := by
  have hdNat : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hd : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hdNat
  have hBreal : 0 < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hend :
      (1 / (B : ℝ)) * valuationPrefixReal p B ≤
        1 / ((p - 1 : ℕ) : ℝ) := by
    calc
      (1 / (B : ℝ)) * valuationPrefixReal p B ≤
          (1 / (B : ℝ)) *
            ((B : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (valuationPrefixReal_le_div_pred hp)
          (one_div_nonneg.mpr hBreal.le)
      _ = 1 / ((p - 1 : ℕ) : ℝ) := by
        field_simp [ne_of_gt hBreal, ne_of_gt hd]
  have hterm (b : ℕ) (hb : b ∈ Finset.Ioc 0 (B - 1)) :
      (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
          valuationPrefixReal p b ≤
        (1 / ((p - 1 : ℕ) : ℝ)) *
          (1 / ((b + 1 : ℕ) : ℝ)) := by
    have hbNat : 0 < b := (Finset.mem_Ioc.mp hb).1
    have hbReal : 0 < (b : ℝ) := by exact_mod_cast hbNat
    have hbSuccReal : 0 < ((b + 1 : ℕ) : ℝ) := by positivity
    have hdiff :
        0 ≤ 1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ) := by
      exact sub_nonneg.mpr (one_div_le_one_div_of_le hbReal (by
        exact_mod_cast Nat.le_add_right b 1))
    calc
      (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
          valuationPrefixReal p b ≤
        (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
          ((b : ℝ) / ((p - 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (valuationPrefixReal_le_div_pred hp) hdiff
      _ = (1 / ((p - 1 : ℕ) : ℝ)) *
          (1 / ((b + 1 : ℕ) : ℝ)) := by
        push_cast
        field_simp [ne_of_gt hbReal, ne_of_gt hbSuccReal, ne_of_gt hd]
        ring
  have hinterior :
      (∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
            valuationPrefixReal p b) ≤
        (1 / ((p - 1 : ℕ) : ℝ)) *
          ∑ b ∈ Finset.Ioc 0 (B - 1),
            1 / ((b + 1 : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b hb ↦ hterm b hb
  have hharm : (harmonic B : ℝ) ≤ 1 + Real.log (B : ℝ) :=
    harmonic_le_one_add_log B
  calc
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : ℝ) / (b : ℝ)) =
        ∑ b ∈ Finset.Icc 1 B,
          (1 / (b : ℝ)) * (b.factorization p : ℝ) := by
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ = (1 / (B : ℝ)) * valuationPrefixReal p B +
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
            valuationPrefixReal p b := weightedFactorizationSum_eq_abel hB
    _ ≤ 1 / ((p - 1 : ℕ) : ℝ) +
        (1 / ((p - 1 : ℕ) : ℝ)) *
          ∑ b ∈ Finset.Ioc 0 (B - 1),
            1 / ((b + 1 : ℕ) : ℝ) := add_le_add hend hinterior
    _ = (1 / ((p - 1 : ℕ) : ℝ)) * (harmonic B : ℝ) := by
      rw [← one_add_sum_Ioc_succ_reciprocal_eq_harmonic hB]
      ring
    _ ≤ (1 / ((p - 1 : ℕ) : ℝ)) *
        (1 + Real.log (B : ℝ)) :=
      mul_le_mul_of_nonneg_left hharm (one_div_nonneg.mpr hd.le)
    _ = (1 + Real.log (B : ℝ)) /
        ((p - 1 : ℕ) : ℝ) := by ring

/-- For primes, the `1/(p-1)` form costs at most a factor two compared with
`1/p`. -/
theorem one_div_prime_pred_le_two_div_prime {p : ℕ} (hp : p.Prime) :
    1 / ((p - 1 : ℕ) : ℝ) ≤ 2 / (p : ℝ) := by
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hdNat : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hd : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hdNat
  apply (div_le_div_iff₀ hd hpReal).2
  norm_num only [one_mul]
  exact_mod_cast (show p ≤ 2 * (p - 1) by omega)

/-- Convenient `O(B/p)` version of the unweighted valuation bound. -/
theorem sum_factorization_Icc_cast_le_two_mul_div_prime
    {p B : ℕ} (hp : p.Prime) :
    (∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)) ≤
      2 * (B : ℝ) / (p : ℝ) := by
  calc
    (∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)) ≤
        (B : ℝ) / ((p - 1 : ℕ) : ℝ) :=
      sum_factorization_Icc_cast_le_div_pred hp
    _ = (B : ℝ) * (1 / ((p - 1 : ℕ) : ℝ)) := by ring
    _ ≤ (B : ℝ) * (2 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left (one_div_prime_pred_le_two_div_prime hp)
        (Nat.cast_nonneg B)
    _ = 2 * (B : ℝ) / (p : ℝ) := by ring

/-- Convenient uniform `O((1 + log B)/p)` version of the weighted bound. -/
theorem weightedFactorizationSum_le_two_mul_one_add_log_div_prime
    {p B : ℕ} (hp : p.Prime) (hB : 1 ≤ B) :
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : ℝ) / (b : ℝ)) ≤
      2 * (1 + Real.log (B : ℝ)) / (p : ℝ) := by
  have hlog : 0 ≤ 1 + Real.log (B : ℝ) := by
    have hcast : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    have hlogNonneg : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg hcast
    linarith
  calc
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : ℝ) / (b : ℝ)) ≤
        (1 + Real.log (B : ℝ)) / ((p - 1 : ℕ) : ℝ) :=
      weightedFactorizationSum_le_one_add_log_div_pred hp hB
    _ = (1 + Real.log (B : ℝ)) *
        (1 / ((p - 1 : ℕ) : ℝ)) := by ring
    _ ≤ (1 + Real.log (B : ℝ)) * (2 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left (one_div_prime_pred_le_two_div_prime hp) hlog
    _ = 2 * (1 + Real.log (B : ℝ)) / (p : ℝ) := by ring

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentPaperCleanListAbsorption -/
section


/-!
# Closing the paper-scale tangent clean-list inequality

This file fixes the moving parameters used in Section 9 of the paper:

* `h = upperTailLength c n = ceil(c n / log n)`;
* `Phead = roughHeadModulus W`;
* `X0 = ceil(n ^ deltaStar)`;
* `y = yNat n = floor(n ^ (2/9))`;
* `W < v <= u <= y` and `u / v <= r0 < 3/2`.

For fixed `W`, `K`, `c`, `r0`, and `deltaStar`, the head-density gap is

`roughHeadDensity W * (2 - r0)`.

We reserve one sixteenth of that gap as the effective list density.  A
slightly conservative explicit version of the paper's one-time cutoff makes
the canonical Selberg main term at most one quarter of the gap.  The
Lambda-squared endpoint remainder and the sharp bank deletion census are
then `o(n/u)`, uniformly for `u <= yNat n`.  The fixed-modulus endpoint loss,
the natural floors and ceilings, and `K*h` are absorbed at the same scale.

Consequently the final candidate-floor-versus-loss inequality is proved
eventually; it is not retained as a premise of the paper-facing wrapper.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Literal Section 9 parameters -/











/-- The natural ceiling dominates the literal real exceptional cutoff. -/
theorem tangentPaperExceptionalCutoff_cast_ge
    (deltaStar : ℝ) (n : ℕ) :
    (n : ℝ) ^ deltaStar ≤
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) := by
  unfold tangentPaperExceptionalCutoff
  exact Nat.le_ceil _









/-! ## The harmonic main term -/





/-! ## Moving-scale negligibility -/





/-! ## Eventual exceptional-loss absorption -/





/-! ## The fixed-head candidate at the paper endpoints -/





/-! ## The literal candidate floor absorbs every canonical loss -/



/-! ## Paper-facing clean-list theorem with no arithmetic loss premise -/

namespace BankPaperRealization



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalChargeAsymptotic -/
section


/-!
# Asymptotic package for the fixed exceptional low-prime charge

This file records the constants and scale arithmetic used after the finite
weighted Selberg decomposition of `G_fix` has been proved.  In the notation
of the paper,

* `paperExceptionalSelbergMainConstant` is `C_S`;
* `paperExceptionalSelbergRemainderConstant` is `C_R`;
* `paperExceptionalChargeConstant c` is `A_exc(c)`;
* `paperExceptionalChargeEpsilon deltaStar n` is the normalized
  endpoint/remainder coefficient.

The finite majorant below is obtained by composing the separate finite
rough/smooth-fibre argument with the elementary valuation-prefix estimates.
Nothing in this file assumes that the actual exceptional charge satisfies
that majorant.  We prove the finite charge bound and its analytic packaging,
together with the independent arithmetic support fact that, under the
displayed paper-range hypotheses, the actual low-prime charge is exactly
zero above twice the paper's literal real exceptional cutoff.  The
corresponding safe integral-cutoff statement is retained as a corollary.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Auditable paper constants -/

















/-! ## The finite Selberg output and its normalized remainder -/











/-! ## The endpoint remainder tends to zero -/





/-! ## Uniform packaging of the finite majorant -/









/-! ## Exact support cutoff for the actual fixed charge -/

/-- A literal exceptional upper factor has smooth part strictly below twice
the paper's real cutoff `n^deltaStar`, once the paper tail lies below `n`.
This is the exact support statement used in the paper's assertion that the
exceptional charge vanishes for `p > 2*n^deltaStar`. -/
theorem completeSmoothPart_cast_lt_two_mul_realExceptionalCutoff
    {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h a : ℕ} (hn : 1 ≤ n) (hh : h ≤ n)
    (ha : a ∈ paperExceptionalUpperFactors n h deltaStar) :
    (completeSmoothPart (yNat n) a : ℝ) <
      2 * (n : ℝ) ^ deltaStar := by
  have haData := mem_paperExceptionalUpperFactors.mp ha
  have haBounds : 2 * n < a ∧ a ≤ 2 * n + h := by
    simpa only [roughUpperBlock, Finset.mem_Ioc] using haData.1
  have haUpper : a ≤ 3 * n := by omega
  let rough := completeRoughLabel (yNat n) a
  let smooth := completeSmoothPart (yNat n) a
  have hroughPos : 0 < rough := completeRoughLabel_pos (yNat n) a
  have hroughR : (0 : ℝ) < rough := by exact_mod_cast hroughPos
  have hsmoothLe : (smooth : ℝ) ≤ (a : ℝ) / (rough : ℝ) := by
    exact Nat.cast_div_le
  have haUpperR : (a : ℝ) ≤ 3 * (n : ℝ) := by
    exact_mod_cast haUpper
  have haDiv : (a : ℝ) / (rough : ℝ) ≤
      3 * (n : ℝ) / (rough : ℝ) :=
    div_le_div_of_nonneg_right haUpperR hroughR.le
  have hexceptional :
      2 * (n : ℝ) / (rough : ℝ) <
        (n : ℝ) ^ deltaStar := by
    simpa only [rough] using haData.2
  have hpowerOne : (1 : ℝ) ≤ (n : ℝ) ^ deltaStar :=
    Real.one_le_rpow (by exact_mod_cast hn) hdeltaNonneg
  have hthree :
      3 * (n : ℝ) / (rough : ℝ) =
        (3 / 2 : ℝ) *
          (2 * (n : ℝ) / (rough : ℝ)) := by ring
  have hthreePower :
      3 * (n : ℝ) / (rough : ℝ) <
        2 * (n : ℝ) ^ deltaStar := by
    rw [hthree]
    nlinarith
  exact hsmoothLe.trans_lt (haDiv.trans_lt hthreePower)

/-- Safe integral-cutoff corollary of the literal real support bound. -/
theorem completeSmoothPart_lt_two_mul_exceptionalCutoff
    {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h a : ℕ} (hn : 1 ≤ n) (hh : h ≤ n)
    (ha : a ∈ paperExceptionalUpperFactors n h deltaStar) :
    completeSmoothPart (yNat n) a <
      2 * tangentPaperExceptionalCutoff deltaStar n := by
  have hsmoothReal :=
    completeSmoothPart_cast_lt_two_mul_realExceptionalCutoff
      hdeltaNonneg hn hh ha
  have hcut := tangentPaperExceptionalCutoff_cast_ge deltaStar n
  have hsmoothCast : (completeSmoothPart (yNat n) a : ℝ) <
      2 * (tangentPaperExceptionalCutoff deltaStar n : ℝ) :=
    hsmoothReal.trans_le
      (mul_le_mul_of_nonneg_left hcut (by norm_num))
  exact_mod_cast hsmoothCast

/-- Every smooth part which actually occurs is contained in the positive
prefix used by the valuation-sum lemmas. -/
theorem paperExceptionalSmoothParts_subset_Icc_two_mul_cutoff
    {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h : ℕ} (hn : 1 ≤ n) (hh : h ≤ n) :
    paperExceptionalSmoothParts n h deltaStar ⊆
      Finset.Icc 1 (2 * tangentPaperExceptionalCutoff deltaStar n) := by
  intro b hb
  obtain ⟨a, haExceptional, hab⟩ :=
    mem_paperExceptionalSmoothParts.mp hb
  have haPos : 0 < a := paperExceptionalUpperFactors_pos haExceptional
  have hbPos : 0 < b := by
    simpa only [hab] using completeSmoothPart_pos
      (y := yNat n) (a := a) haPos
  have hbLt : b < 2 * tangentPaperExceptionalCutoff deltaStar n := by
    simpa only [hab] using
      completeSmoothPart_lt_two_mul_exceptionalCutoff
        hdeltaNonneg hn hh haExceptional
  exact Finset.mem_Icc.mpr ⟨hbPos, hbLt.le⟩

/-! ## Closing the finite weighted Selberg estimate -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedGuardResidual -/
section


/-!
# Signed exceptional and guard residual ledger

This module gives literal names to the two signed terms in the final rough
residual identity.  They are intentionally separate from the nonnegative
fixed-factor charge used for divisibility.

`roughCanonicalSignedExceptionalResidual` is the exceptional-row portion of
the raw upper-minus-lower comparison.  The order of its two finite sums is
not replaced by a sum of absolute values.  `roughCanonicalAggregateGuardResidual`
is the paper's three-term guard difference: restored raw weights deleted in
nonexceptional rows, restored exceptional donors, and the negative bank-base
charge.

The exact four-term sign convention and its triangle reduction are proved at
the end.  The aggregate guard term is bounded and absorbed unconditionally
from the literal finite census, and the correction-pool valuation census is
also closed by the global Legendre prefix bound.  The genuinely signed
exceptional estimate and the uniform correction-density estimate remain
exposed as named propositions rather than being confused with the already
proved nonnegative exceptional charge bound.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Elementary finite valuation envelopes -/







/-! ## Literal signed exceptional term -/







/-- The upper half of the signed exceptional term is exactly the valuation
of the product of all literal exceptional upper factors. -/
theorem sum_paperExceptionalUpperFactors_factorization_eq_prod
    (n h : Nat) (deltaStar : Real) (p : Nat) :
    (∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
        (a.factorization p : Real)) =
      (((paperExceptionalUpperFactors n h deltaStar).prod id).factorization p :
        Real) := by
  have hNat :
      ((paperExceptionalUpperFactors n h deltaStar).prod id).factorization p =
        ∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
          a.factorization p :=
    Nat.factorization_prod_apply
      (fun (a : Nat) ha ↦ (paperExceptionalUpperFactors_pos ha).ne')
  rw [hNat]
  push_cast
  rfl



/-! ## Literal aggregate guard difference -/

















/-! ## A uniform finite guard-profile bound -/











/-! ## Uniform absorption of the guard majorant -/















/-! ## Literal aggregate nonsmooth row correction -/





















/-! ## Exact final sign ledger and quantitative reduction -/





























end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalCoreFirst -/
section


/-!
# Core-first cancellation for the signed exceptional residual

The exceptional term in Section 9 cannot be estimated by separating its
positive and negative halves.  The paper first fixes the complete smooth
core `b`, sums all physical rough pieces with that core, and only then takes
absolute values.  This file makes that order of summation literal.

The first part is completely finite.  It partitions both halves of
`roughCanonicalSignedExceptionalResidual` by `completeSmoothPart (yNat n)`,
transfers every low-prime valuation to that smooth part, and reindexes both
halves over one common positive prefix.  Thus the sign in each core is the
actual upper cardinality minus the actual weighted lower mass.

The second part records the elementary fixed-head cancellation used on the
leading term.  Its periodic coefficient has uniformly bounded partial sums;
finite Abel summation therefore bounds it against every sequence with the
paper's prime-power-by-prime-power variation estimate.  No rough-counting
asymptotic is used in these arguments.

The last part isolates the one genuinely new analytic input: the signed
four-to-five-prime chamber expansion for a fixed smooth core, before any
valuation sum or triangle inequality.  All subsequent core, valuation, and
endpoint ledgers are finite consequences of that expansion.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.LocalFugacityBounds

noncomputable section

namespace BankPaperRealization

/-! ## The literal common smooth-core partition -/









/-- Every literal raw lower candidate is positive and at most `2*n`. -/
theorem roughRawCandidateSet_pos_le_two_mul
    {n h K a : Nat} (ha : a ∈ roughRawCandidateSet n h K) :
    0 < a ∧ a ≤ 2 * n := by
  rw [roughRawCandidateSet, Finset.mem_union] at ha
  rcases ha with ha | ha
  · rw [roughHighLowerBlock, Finset.mem_Ioc] at ha
    omega
  · rw [roughBroadLowerBlock, Finset.mem_Ioc] at ha
    omega

/-- In an exceptional lower row the complete smooth core is already below
the paper's real exceptional cutoff.  No enlargement to a positive charge
has occurred here. -/
theorem completeSmoothPart_cast_lt_realExceptionalCutoff_of_rawLower
    {n h K a : Nat} {deltaStar : Real}
    (ha : a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar) :
    (completeSmoothPart (yNat n) a : Real) < (n : Real) ^ deltaStar := by
  have haData := mem_roughCanonicalExceptionalRawLowerSet.mp ha
  have haBounds := roughRawCandidateSet_pos_le_two_mul haData.1
  let rough := completeRoughLabel (yNat n) a
  let smooth := completeSmoothPart (yNat n) a
  have hroughPos : 0 < rough := completeRoughLabel_pos (yNat n) a
  have hroughReal : (0 : Real) < (rough : Real) := by
    exact_mod_cast hroughPos
  have hsmoothLe : (smooth : Real) ≤ (a : Real) / (rough : Real) := by
    exact Nat.cast_div_le
  have haLeReal : (a : Real) ≤ 2 * (n : Real) := by
    exact_mod_cast haBounds.2
  have hdivLe : (a : Real) / (rough : Real) ≤
      2 * (n : Real) / (rough : Real) :=
    div_le_div_of_nonneg_right haLeReal hroughReal.le
  have hexceptional :
      2 * (n : Real) / (rough : Real) < (n : Real) ^ deltaStar := by
    simpa only [rough, RoughCanonicalExceptionalLabel] using haData.2
  exact hsmoothLe.trans_lt (hdivLe.trans_lt hexceptional)

/-- Natural-ceiling form of the preceding strict smooth-core cutoff. -/
theorem completeSmoothPart_lt_exceptionalCutoff_of_rawLower
    {n h K a : Nat} {deltaStar : Real}
    (ha : a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar) :
    completeSmoothPart (yNat n) a <
      tangentPaperExceptionalCutoff deltaStar n := by
  have hsmooth :=
    completeSmoothPart_cast_lt_realExceptionalCutoff_of_rawLower ha
  have hcut := tangentPaperExceptionalCutoff_cast_ge deltaStar n
  exact_mod_cast hsmooth.trans_le hcut

/-- All lower smooth cores lie in the same safe prefix already used for the
upper exceptional factors. -/
theorem roughCanonicalExceptionalRawLowerSmoothParts_subset_Icc_two_mul_cutoff
    {n h K : Nat} {deltaStar : Real} :
    roughCanonicalExceptionalRawLowerSmoothParts n h K deltaStar ⊆
      Finset.Icc 1 (2 * tangentPaperExceptionalCutoff deltaStar n) := by
  intro b hb
  obtain ⟨a, ha, hab⟩ :=
    mem_roughCanonicalExceptionalRawLowerSmoothParts.mp hb
  have haData := mem_roughCanonicalExceptionalRawLowerSet.mp ha
  have haPos := (roughRawCandidateSet_pos_le_two_mul haData.1).1
  have hbPos : 0 < b := by
    simpa only [hab] using
      completeSmoothPart_pos (y := yNat n) (a := a) haPos
  have hbLt : b < tangentPaperExceptionalCutoff deltaStar n := by
    simpa only [hab] using
      completeSmoothPart_lt_exceptionalCutoff_of_rawLower ha
  exact Finset.mem_Icc.mpr ⟨hbPos, by omega⟩

/-- A low-prime valuation lives entirely on the complete smooth core. -/
theorem factorization_eq_completeSmoothPart_factorization_of_le
    {n a p : Nat} (hp : p ≤ yNat n) :
    (a.factorization p : Real) =
      ((completeSmoothPart (yNat n) a).factorization p : Real) := by
  rw [completeSmoothPart_factorization_apply, if_pos hp]

/-- A prescribed upper smooth fibre is empty when its core is not in the
corresponding image. -/
theorem paperExceptionalSmoothFiber_eq_empty_of_not_mem
    {n h b : Nat} {deltaStar : Real}
    (hb : b ∉ paperExceptionalSmoothParts n h deltaStar) :
    paperExceptionalSmoothFiber n h deltaStar b = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have haData := mem_paperExceptionalSmoothFiber.mp ha
  exact hb (mem_paperExceptionalSmoothParts.mpr
    ⟨a, haData.1, haData.2⟩)

/-- A prescribed lower smooth fibre is empty when its core is not in the
corresponding image. -/
theorem roughCanonicalExceptionalRawLowerSmoothFiber_eq_empty_of_not_mem
    {n h K b : Nat} {deltaStar : Real}
    (hb : b ∉ roughCanonicalExceptionalRawLowerSmoothParts
      n h K deltaStar) :
    roughCanonicalExceptionalRawLowerSmoothFiber n h K deltaStar b = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have haData := mem_roughCanonicalExceptionalRawLowerSmoothFiber.mp ha
  exact hb (mem_roughCanonicalExceptionalRawLowerSmoothParts.mpr
    ⟨a, haData.1, haData.2⟩)



/-- The upper valuation sum grouped first by its complete smooth core. -/
theorem sum_paperExceptionalUpperFactors_factorization_eq_corePrefix
    {n h p : Nat} {deltaStar : Real}
    (hdelta : 0 ≤ deltaStar) (hn : 1 ≤ n) (hh : h ≤ n)
    (hp : p ≤ yNat n) :
    (∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
        (a.factorization p : Real)) =
      ∑ b ∈ Finset.Icc 1
          (2 * tangentPaperExceptionalCutoff deltaStar n),
        (b.factorization p : Real) *
          ((paperExceptionalSmoothFiber n h deltaStar b).card : Real) := by
  let smoothParts := paperExceptionalSmoothParts n h deltaStar
  have hsubset : smoothParts ⊆ Finset.Icc 1
      (2 * tangentPaperExceptionalCutoff deltaStar n) :=
    paperExceptionalSmoothParts_subset_Icc_two_mul_cutoff
      hdelta hn hh
  have hprod :=
    paperExceptionalUpperFactors_prod_factorization_eq_smoothFiberSum
      (n := n) (h := h) (p := p) (deltaStar := deltaStar) hp
  calc
    (∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
        (a.factorization p : Real)) =
        (((paperExceptionalUpperFactors n h deltaStar).prod id).factorization p :
          Real) :=
      sum_paperExceptionalUpperFactors_factorization_eq_prod
        n h deltaStar p
    _ = ∑ b ∈ smoothParts,
        (b.factorization p : Real) *
          ((paperExceptionalSmoothFiber n h deltaStar b).card : Real) := by
      exact_mod_cast hprod
    _ = ∑ b ∈ Finset.Icc 1
          (2 * tangentPaperExceptionalCutoff deltaStar n),
        (b.factorization p : Real) *
          ((paperExceptionalSmoothFiber n h deltaStar b).card : Real) := by
      apply Finset.sum_subset hsubset
      intro b _hbPrefix hbNotSmooth
      rw [paperExceptionalSmoothFiber_eq_empty_of_not_mem hbNotSmooth]
      simp

/-- The weighted lower valuation sum grouped first by its complete smooth
core and extended by zero to the same prefix as the upper half. -/
theorem sum_roughCanonicalExceptionalRawLower_factorization_eq_corePrefix
    {n h K p : Nat} {deltaStar : Real} {rawWeight : Nat → Real}
    (hp : p ≤ yNat n) :
    (∑ a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar,
        rawWeight a * (a.factorization p : Real)) =
      ∑ b ∈ Finset.Icc 1
          (2 * tangentPaperExceptionalCutoff deltaStar n),
        (b.factorization p : Real) *
          (∑ a ∈ roughCanonicalExceptionalRawLowerSmoothFiber
              n h K deltaStar b, rawWeight a) := by
  let lower := roughCanonicalExceptionalRawLowerSet n h K deltaStar
  let smooth := completeSmoothPart (yNat n)
  let smoothParts :=
    roughCanonicalExceptionalRawLowerSmoothParts n h K deltaStar
  have hsubset : smoothParts ⊆ Finset.Icc 1
      (2 * tangentPaperExceptionalCutoff deltaStar n) :=
    roughCanonicalExceptionalRawLowerSmoothParts_subset_Icc_two_mul_cutoff
  calc
    (∑ a ∈ lower, rawWeight a * (a.factorization p : Real)) =
        ∑ a ∈ lower,
          rawWeight a * ((smooth a).factorization p : Real) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [factorization_eq_completeSmoothPart_factorization_of_le hp]
    _ = ∑ b ∈ smoothParts,
        ∑ a ∈ lower.filter (fun a => smooth a = b),
          rawWeight a * ((smooth a).factorization p : Real) := by
      exact (Finset.sum_fiberwise_of_maps_to
        (s := lower) (t := lower.image smooth) (g := smooth)
        (fun a ha => Finset.mem_image_of_mem smooth ha)
        (fun a => rawWeight a * ((smooth a).factorization p : Real))).symm
    _ = ∑ b ∈ smoothParts,
        ∑ a ∈ roughCanonicalExceptionalRawLowerSmoothFiber
            n h K deltaStar b,
          rawWeight a * (b.factorization p : Real) := by
      apply Finset.sum_congr rfl
      intro b _hb
      apply Finset.sum_congr
      · rfl
      · intro a ha
        have hab : smooth a = b := (Finset.mem_filter.mp ha).2
        rw [hab]
    _ = ∑ b ∈ smoothParts,
        (b.factorization p : Real) *
          (∑ a ∈ roughCanonicalExceptionalRawLowerSmoothFiber
              n h K deltaStar b, rawWeight a) := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = ∑ b ∈ Finset.Icc 1
          (2 * tangentPaperExceptionalCutoff deltaStar n),
        (b.factorization p : Real) *
          (∑ a ∈ roughCanonicalExceptionalRawLowerSmoothFiber
              n h K deltaStar b, rawWeight a) := by
      apply Finset.sum_subset hsubset
      intro b _hbPrefix hbNotSmooth
      rw [roughCanonicalExceptionalRawLowerSmoothFiber_eq_empty_of_not_mem
        hbNotSmooth]
      simp

/-- Exact core-first identity for the signed exceptional residual.  The
subtraction remains inside the `b`-sum; no positive-parts majorant appears. -/
theorem roughCanonicalSignedExceptionalResidual_eq_coreFirst
    {n h K p : Nat} {deltaStar : Real} {rawWeight : Nat → Real}
    (hdelta : 0 ≤ deltaStar) (hn : 1 ≤ n) (hh : h ≤ n)
    (hp : p ≤ yNat n) :
    roughCanonicalSignedExceptionalResidual n h K deltaStar
        rawWeight p =
      ∑ b ∈ Finset.Icc 1
          (2 * tangentPaperExceptionalCutoff deltaStar n),
        (b.factorization p : Real) *
          roughCanonicalSignedExceptionalCoreMass n h K deltaStar
            rawWeight b := by
  rw [roughCanonicalSignedExceptionalResidual,
    sum_paperExceptionalUpperFactors_factorization_eq_corePrefix
      hdelta hn hh hp,
    sum_roughCanonicalExceptionalRawLower_factorization_eq_corePrefix hp,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _hb
  unfold roughCanonicalSignedExceptionalCoreMass
  ring

/-! ## The fixed-head periodic coefficient -/



/-- Multiplication by an integer coprime to the head modulus preserves the
periodic core coefficient exactly. -/
theorem roughHeadPeriodicCoreCoefficient_mul_left
    {W D b : Nat} (hD : Nat.Coprime D (roughHeadModulus W)) :
    roughHeadPeriodicCoreCoefficient W (D * b) =
      roughHeadPeriodicCoreCoefficient W b := by
  unfold roughHeadPeriodicCoreCoefficient
  by_cases hb : Nat.Coprime b (roughHeadModulus W)
  · have hDb : Nat.Coprime (D * b) (roughHeadModulus W) :=
      (Nat.coprime_mul_iff_left).2 ⟨hD, hb⟩
    rw [if_pos hDb, if_pos hb]
  · have hDb : ¬Nat.Coprime (D * b) (roughHeadModulus W) := by
      intro h
      exact hb (Nat.coprime_mul_iff_left.mp h).2
    rw [if_neg hDb, if_neg hb]



/-- The partial sum is exactly the reduced-residue discrepancy divided by
the fixed density. -/
theorem roughHeadPeriodicCorePrefix_eq
    (W B : Nat) :
    roughHeadPeriodicCorePrefix W B =
      (B : Real) -
        ((roughHeadFree W (Finset.Icc 1 B)).card : Real) /
          roughHeadDensity W := by
  have hcard : (Finset.Icc 1 B).card = B := by simp
  unfold roughHeadPeriodicCorePrefix roughHeadPeriodicCoreCoefficient
  calc
    (∑ b ∈ Finset.Icc 1 B,
        (1 - if Nat.Coprime b (roughHeadModulus W) then
          1 / roughHeadDensity W else 0)) =
        (∑ _b ∈ Finset.Icc 1 B, (1 : Real)) -
          ∑ b ∈ Finset.Icc 1 B,
            (if Nat.Coprime b (roughHeadModulus W) then
              1 / roughHeadDensity W else 0) := by
      rw [Finset.sum_sub_distrib]
    _ = ((Finset.Icc 1 B).card : Real) -
          ((roughHeadFree W (Finset.Icc 1 B)).card : Real) /
            roughHeadDensity W := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [show (∑ b ∈ Finset.Icc 1 B,
          if Nat.Coprime b (roughHeadModulus W) then
            1 / roughHeadDensity W else 0) =
          ((roughHeadFree W (Finset.Icc 1 B)).card : Real) /
            roughHeadDensity W by
        rw [← Finset.sum_filter]
        simp [roughHeadFree]
        ring]
    _ = (B : Real) -
          ((roughHeadFree W (Finset.Icc 1 B)).card : Real) /
            roughHeadDensity W := by rw [hcard]

/-- Every partial sum of the mean-zero coefficient is bounded by one fixed
head-modulus constant. -/
theorem abs_roughHeadPeriodicCorePrefix_le
    (W B : Nat) :
    |roughHeadPeriodicCorePrefix W B| ≤
      (roughHeadModulus W : Real) / roughHeadDensity W := by
  have hset : Finset.Icc 1 B = Finset.Ioc 0 B := by
    ext b
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hcount := roughHeadFree_Ioc_card_error_le
    (W := W) (lo := 0) (hi := B) (Nat.zero_le B)
  rw [Nat.cast_sub (Nat.zero_le B), Nat.cast_zero, sub_zero] at hcount
  have hdelta : 0 < roughHeadDensity W := roughHeadDensity_pos W
  rw [roughHeadPeriodicCorePrefix_eq, hset]
  have hidentity :
      (B : Real) -
          ((roughHeadFree W (Finset.Ioc 0 B)).card : Real) /
            roughHeadDensity W =
        -(((roughHeadFree W (Finset.Ioc 0 B)).card : Real) -
            roughHeadDensity W * (B : Real)) /
          roughHeadDensity W := by
    field_simp [hdelta.ne']
    ring
  rw [hidentity, abs_div, abs_neg, abs_of_pos hdelta]
  exact div_le_div_of_nonneg_right hcount hdelta.le



/-- A coprime multiplier leaves every periodic prefix unchanged. -/
theorem roughHeadPeriodicCoreMulPrefix_eq
    {W D B : Nat} (hD : Nat.Coprime D (roughHeadModulus W)) :
    roughHeadPeriodicCoreMulPrefix W D B =
      roughHeadPeriodicCorePrefix W B := by
  unfold roughHeadPeriodicCoreMulPrefix roughHeadPeriodicCorePrefix
  apply Finset.sum_congr rfl
  intro b _hb
  exact roughHeadPeriodicCoreCoefficient_mul_left hD

/-- Consequently the same explicit prefix bound is uniform in every
coprime multiplier. -/
theorem abs_roughHeadPeriodicCoreMulPrefix_le
    {W D B : Nat} (hD : Nat.Coprime D (roughHeadModulus W)) :
    |roughHeadPeriodicCoreMulPrefix W D B| ≤
      (roughHeadModulus W : Real) / roughHeadDensity W := by
  rw [roughHeadPeriodicCoreMulPrefix_eq hD]
  exact abs_roughHeadPeriodicCorePrefix_le W B

/-! ## Finite Abel cancellation -/





/-- The zero-extended periodic coefficient has the expected positive
prefix sum. -/
theorem sum_range_succ_zeroExtendedPeriodicCore_eq
    (W D B : Nat) :
    (∑ b ∈ Finset.range (B + 1),
        if b = 0 then 0 else
          roughHeadPeriodicCoreCoefficient W (D * b)) =
      roughHeadPeriodicCoreMulPrefix W D B := by
  rw [Nat.range_eq_Icc_zero_sub_one _ (Nat.add_one_ne_zero B),
    Nat.add_sub_cancel_right]
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le B), Finset.sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc]
  unfold roughHeadPeriodicCoreMulPrefix
  simp only [if_pos, zero_add]
  apply Finset.sum_congr rfl
  intro b hb
  have hbOne : 1 ≤ b := (Finset.mem_Icc.mp hb).1
  have hb0 : b ≠ 0 := by omega
  simp only [hb0, if_false]

/-- Exact finite Abel identity for the weighted periodic core sum. -/
theorem roughHeadPeriodicWeightedCoreSum_eq_abel
    {W D B : Nat} {F : Nat → Real} (hB : 1 ≤ B) :
    roughHeadPeriodicWeightedCoreSum W D F B =
      F B * roughHeadPeriodicCoreMulPrefix W D B +
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (F b - F (b + 1)) *
            roughHeadPeriodicCoreMulPrefix W D b := by
  have hBpos : 0 < B := by omega
  have habel := Finset.sum_Ioc_by_parts
    (f := F)
    (g := fun b : Nat => if b = 0 then 0 else
      roughHeadPeriodicCoreCoefficient W (D * b))
    (m := 0) (n := B) hBpos
  have hIoc : Finset.Ioc 0 B = Finset.Icc 1 B := by
    simpa only [zero_add] using
      (Finset.Icc_add_one_left_eq_Ioc 0 B).symm
  rw [hIoc] at habel
  simp_rw [sum_range_succ_zeroExtendedPeriodicCore_eq] at habel
  have hlhs :
      (∑ b ∈ Finset.Icc 1 B,
        F b • (if b = 0 then 0 else
          roughHeadPeriodicCoreCoefficient W (D * b))) =
        roughHeadPeriodicWeightedCoreSum W D F B := by
    unfold roughHeadPeriodicWeightedCoreSum
    apply Finset.sum_congr rfl
    intro b hb
    have hbOne : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hb0 : b ≠ 0 := by omega
    simp only [hb0, if_false, smul_eq_mul]
  rw [hlhs] at habel
  simp only [smul_eq_mul, zero_add] at habel
  have hprefixZero : roughHeadPeriodicCoreMulPrefix W D 0 = 0 := by
    simp [roughHeadPeriodicCoreMulPrefix]
  rw [hprefixZero, mul_zero, sub_zero] at habel
  have hneg :
      -(∑ b ∈ Finset.Ioc 0 (B - 1),
          (F (b + 1) - F b) * roughHeadPeriodicCoreMulPrefix W D b) =
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (F b - F (b + 1)) *
            roughHeadPeriodicCoreMulPrefix W D b := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  calc
    roughHeadPeriodicWeightedCoreSum W D F B =
        F B * roughHeadPeriodicCoreMulPrefix W D B -
          ∑ b ∈ Finset.Ioc 0 (B - 1),
            (F (b + 1) - F b) *
              roughHeadPeriodicCoreMulPrefix W D b := habel
    _ = _ := by rw [sub_eq_add_neg, hneg]

/-- A bounded periodic prefix controls every finite weighted sum by the
discrete variation of its weight. -/
theorem abs_roughHeadPeriodicWeightedCoreSum_le_variation
    {W D B : Nat} {F : Nat → Real}
    (hD : Nat.Coprime D (roughHeadModulus W)) :
    |roughHeadPeriodicWeightedCoreSum W D F B| ≤
      ((roughHeadModulus W : Real) / roughHeadDensity W) *
        roughCoreDiscreteVariation F B := by
  by_cases hB0 : B = 0
  · subst B
    simp [roughHeadPeriodicWeightedCoreSum, roughCoreDiscreteVariation]
  have hB : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB0
  rw [roughHeadPeriodicWeightedCoreSum_eq_abel hB,
    roughCoreDiscreteVariation, if_neg hB0]
  have hprefix (b : Nat) :
      |roughHeadPeriodicCoreMulPrefix W D b| ≤
        (roughHeadModulus W : Real) / roughHeadDensity W :=
    abs_roughHeadPeriodicCoreMulPrefix_le hD
  have hconstantNonneg :
      0 ≤ (roughHeadModulus W : Real) / roughHeadDensity W := by
    exact div_nonneg (Nat.cast_nonneg _) (roughHeadDensity_pos W).le
  calc
    |F B * roughHeadPeriodicCoreMulPrefix W D B +
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (F b - F (b + 1)) *
            roughHeadPeriodicCoreMulPrefix W D b| ≤
      |F B * roughHeadPeriodicCoreMulPrefix W D B| +
        |∑ b ∈ Finset.Ioc 0 (B - 1),
          (F b - F (b + 1)) *
            roughHeadPeriodicCoreMulPrefix W D b| := abs_add_le _ _
    _ ≤ |F B| * ((roughHeadModulus W : Real) / roughHeadDensity W) +
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          |F b - F (b + 1)| *
            ((roughHeadModulus W : Real) / roughHeadDensity W) := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hprefix B) (abs_nonneg _)
      · exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun b _hb => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hprefix b) (abs_nonneg _))
    _ = ((roughHeadModulus W : Real) / roughHeadDensity W) *
        (|F B| + ∑ b ∈ Finset.Ioc 0 (B - 1),
          |F b - F (b + 1)|) := by
      rw [mul_add, Finset.mul_sum]
      apply congrArg₂ (fun x y : Real => x + y)
      · ring
      · apply Finset.sum_congr rfl
        intro b _hb
        ring

/-! ## Prime-power expansion of the periodic leading ledger -/

/-- Exact reindexing of a weighted divisibility column by division. -/
theorem sum_Icc_mul_divInd_eq_quotientSum
    {D B : Nat} (hD : 0 < D) (F : Nat → Real) :
    (∑ b ∈ Finset.Icc 1 B, F b * divInd D b) =
      ∑ m ∈ Finset.Icc 1 (B / D), F (D * m) := by
  have hfilter :
      (∑ b ∈ Finset.Icc 1 B, F b * divInd D b) =
        ∑ b ∈ (Finset.Icc 1 B).filter (fun b => D ∣ b), F b := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _hb
    by_cases hDb : D ∣ b <;> simp [divInd, hDb]
  rw [hfilter]
  symm
  apply Finset.sum_bij (fun m _hm => D * m)
  · intro m hm
    have hmData := Finset.mem_Icc.mp hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Nat.dvd_mul_right D m⟩
    · exact mul_pos hD hmData.1
    · simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hD).mp hmData.2
  · intro m₁ _hm₁ m₂ _hm₂ heq
    exact Nat.mul_left_cancel hD heq
  · intro b hb
    have hbData := Finset.mem_filter.mp hb
    have hbIcc := Finset.mem_Icc.mp hbData.1
    have hDLeB : D ≤ b := Nat.le_of_dvd hbIcc.1 hbData.2
    refine ⟨b / D, Finset.mem_Icc.mpr ⟨Nat.div_pos hDLeB hD,
      Nat.div_le_div_right hbIcc.2⟩, ?_⟩
    simpa only [Nat.mul_comm] using Nat.mul_div_cancel' hbData.2
  · intro m _hm
    rfl



/-- Expanding the valuation into prime-power divisibility columns and then
dividing by `p^k` gives the exact sum of periodic Abel blocks. -/
theorem roughHeadPeriodicValuationCoreSum_eq_primePowerBlocks
    {W p B : Nat} (hp : p.Prime) (F : Nat → Real) :
    roughHeadPeriodicValuationCoreSum W p F B =
      ∑ k ∈ positiveExponents B,
        roughHeadPeriodicWeightedCoreSum W (p ^ k)
          (fun m => F (p ^ k * m)) (B / p ^ k) := by
  unfold roughHeadPeriodicValuationCoreSum
  calc
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : Real) *
          roughHeadPeriodicCoreCoefficient W b * F b) =
      ∑ b ∈ Finset.Icc 1 B,
        (∑ k ∈ positiveExponents B, divInd (p ^ k) b) *
          roughHeadPeriodicCoreCoefficient W b * F b := by
      apply Finset.sum_congr rfl
      intro b hb
      have hbData := Finset.mem_Icc.mp hb
      have hvaluation :=
        valuation_eq_sum_divInd_of_le hp hbData.1 hbData.2
      change valuation p b * roughHeadPeriodicCoreCoefficient W b * F b = _
      rw [hvaluation]
    _ = ∑ b ∈ Finset.Icc 1 B,
        ∑ k ∈ positiveExponents B,
          (roughHeadPeriodicCoreCoefficient W b * F b) *
            divInd (p ^ k) b := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = ∑ k ∈ positiveExponents B,
        ∑ b ∈ Finset.Icc 1 B,
          (roughHeadPeriodicCoreCoefficient W b * F b) *
            divInd (p ^ k) b := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ positiveExponents B,
        ∑ m ∈ Finset.Icc 1 (B / p ^ k),
          roughHeadPeriodicCoreCoefficient W (p ^ k * m) *
            F (p ^ k * m) := by
      apply Finset.sum_congr rfl
      intro k _hk
      simpa only [mul_comm] using
        (sum_Icc_mul_divInd_eq_quotientSum
          (pow_pos hp.pos k)
          (fun b => roughHeadPeriodicCoreCoefficient W b * F b))
    _ = ∑ k ∈ positiveExponents B,
        roughHeadPeriodicWeightedCoreSum W (p ^ k)
          (fun m => F (p ^ k * m)) (B / p ^ k) := by
      apply Finset.sum_congr rfl
      intro k _hk
      unfold roughHeadPeriodicWeightedCoreSum
      apply Finset.sum_congr rfl
      intro m _hm
      ring

/-- The paper's periodic prime-power lemma in its exact reusable form.  The
only hypothesis on `F` is the `O(1/p^k)` discrete variation which a bounded
`C^1` logarithmic kernel divided by its argument satisfies. -/
theorem abs_roughHeadPeriodicValuationCoreSum_le
    {W p B : Nat} {F : Nat → Real} {variationConstant : Real}
    (hp : p.Prime) (hWp : W < p) (hvariationNonneg : 0 ≤ variationConstant)
    (hvariation : ∀ k ∈ positiveExponents B,
      roughCoreDiscreteVariation (fun m => F (p ^ k * m))
          (B / p ^ k) ≤ variationConstant / ((p ^ k : Nat) : Real)) :
    |roughHeadPeriodicValuationCoreSum W p F B| ≤
      2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
        variationConstant / (p : Real) := by
  rw [roughHeadPeriodicValuationCoreSum_eq_primePowerBlocks hp F]
  have hpReal : (0 : Real) < (p : Real) := by exact_mod_cast hp.pos
  have hheadNonneg :
      0 ≤ (roughHeadModulus W : Real) / roughHeadDensity W := by
    exact div_nonneg (Nat.cast_nonneg _) (roughHeadDensity_pos W).le
  have hblock (k : Nat) (hk : k ∈ positiveExponents B) :
      |roughHeadPeriodicWeightedCoreSum W (p ^ k)
          (fun m => F (p ^ k * m)) (B / p ^ k)| ≤
        ((roughHeadModulus W : Real) / roughHeadDensity W) *
          (variationConstant / ((p ^ k : Nat) : Real)) := by
    have hcop : Nat.Coprime (p ^ k) (roughHeadModulus W) :=
      (prime_coprime_roughHeadModulus_of_cutoff_lt hp hWp).pow_left k
    exact (abs_roughHeadPeriodicWeightedCoreSum_le_variation
      (F := fun m => F (p ^ k * m)) (B := B / p ^ k) hcop).trans
        (mul_le_mul_of_nonneg_left (hvariation k hk) hheadNonneg)
  calc
    |∑ k ∈ positiveExponents B,
        roughHeadPeriodicWeightedCoreSum W (p ^ k)
          (fun m => F (p ^ k * m)) (B / p ^ k)| ≤
      ∑ k ∈ positiveExponents B,
        |roughHeadPeriodicWeightedCoreSum W (p ^ k)
          (fun m => F (p ^ k * m)) (B / p ^ k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ positiveExponents B,
        ((roughHeadModulus W : Real) / roughHeadDensity W) *
          (variationConstant / ((p ^ k : Nat) : Real)) :=
      Finset.sum_le_sum hblock
    _ = ((roughHeadModulus W : Real) / roughHeadDensity W) *
        variationConstant *
          (∑ k ∈ positiveExponents B,
            1 / ((p ^ k : Nat) : Real)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ ≤ ((roughHeadModulus W : Real) / roughHeadDensity W) *
        variationConstant * (2 / (p : Real)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [positiveExponents, zero_add, pow_one] using
          (sum_inv_pow_tail_le (p := p) (r := 0) (A := B) hp.two_le)
      · exact mul_nonneg hheadNonneg hvariationNonneg
    _ = 2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
        variationConstant / (p : Real) := by ring

/-! ## Elementary valuation ledgers for the analytic remainders -/

/-- A pointwise `A/b+E` core error sums with the two standard valuation
prefixes and no loss beyond their literal constants. -/
theorem abs_sum_factorization_mul_error_le
    {p B : Nat} {error : Nat → Real} {A E : Real}
    (hp : p.Prime) (hB : 1 ≤ B) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (herror : ∀ b ∈ Finset.Icc 1 B,
      |error b| ≤ A / (b : Real) + E) :
    |∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : Real) * error b| ≤
      A * (2 * (1 + Real.log (B : Real)) / (p : Real)) +
        E * (2 * (B : Real) / (p : Real)) := by
  have hpReal : (0 : Real) < (p : Real) := by exact_mod_cast hp.pos
  have hweighted :=
    weightedFactorizationSum_le_two_mul_one_add_log_div_prime
      (p := p) (B := B) hp hB
  have hunweighted :=
    sum_factorization_Icc_cast_le_two_mul_div_prime
      (p := p) (B := B) hp
  have hmainNonneg : 0 ≤ A := hA
  have hendNonneg : 0 ≤ E := hE
  calc
    |∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : Real) * error b| ≤
      ∑ b ∈ Finset.Icc 1 B,
        |(b.factorization p : Real) * error b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : Real) * |error b| := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : Real) * (A / (b : Real) + E) := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (herror b hb) (Nat.cast_nonneg _)
    _ = A * (∑ b ∈ Finset.Icc 1 B,
          (b.factorization p : Real) / (b : Real)) +
        E * (∑ b ∈ Finset.Icc 1 B,
          (b.factorization p : Real)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ ≤ A * (2 * (1 + Real.log (B : Real)) / (p : Real)) +
        E * (2 * (B : Real) / (p : Real)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hweighted hmainNonneg)
        (mul_le_mul_of_nonneg_left hunweighted hendNonneg)

/-- The valuation count in the single cutoff band is bounded by the full
prefix count. -/
theorem sum_factorization_cutoffBand_le_four_mul_div_prime
    {p X : Nat} (hp : p.Prime) (_hX : 1 ≤ X) :
    (∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real)) ≤
      4 * (X : Real) / (p : Real) := by
  have hsubset : Finset.Ioc (X / 2) (2 * X) ⊆
      Finset.Icc 1 (2 * X) := by
    intro b hb
    have hbData := Finset.mem_Ioc.mp hb
    exact Finset.mem_Icc.mpr ⟨by omega, hbData.2⟩
  calc
    (∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real)) ≤
      ∑ b ∈ Finset.Icc 1 (2 * X),
        (b.factorization p : Real) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _b _hbPrefix _hbBand => Nat.cast_nonneg _)
    _ ≤ 2 * ((2 * X : Nat) : Real) / (p : Real) :=
      sum_factorization_Icc_cast_le_two_mul_div_prime hp
    _ = 4 * (X : Real) / (p : Real) := by
      push_cast
      ring

/-- Because every member of the cutoff band is larger than `X/2`, its
harmonically weighted valuation sum is `O(1/p)`, not `O(log X/p)`. -/
theorem weightedFactorizationSum_cutoffBand_le_eight_div_prime
    {p X : Nat} (hp : p.Prime) (hX : 1 ≤ X) :
    (∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real) / (b : Real)) ≤
      8 / (p : Real) := by
  have hXReal : (0 : Real) < (X : Real) := by exact_mod_cast hX
  have hpReal : (0 : Real) < (p : Real) := by exact_mod_cast hp.pos
  have hpoint (b : Nat) (hb : b ∈ Finset.Ioc (X / 2) (2 * X)) :
      (b.factorization p : Real) / (b : Real) ≤
        (2 / (X : Real)) * (b.factorization p : Real) := by
    have hbData := Finset.mem_Ioc.mp hb
    have hbPos : 0 < b := by omega
    have hbReal : (0 : Real) < (b : Real) := by exact_mod_cast hbPos
    have hXLe : X ≤ 2 * b := by omega
    have hrecip : 1 / (b : Real) ≤ 2 / (X : Real) := by
      apply (div_le_div_iff₀ hbReal hXReal).2
      have hXLeReal : (X : Real) ≤ 2 * (b : Real) := by
        exact_mod_cast hXLe
      simpa only [one_mul] using hXLeReal
    calc
      (b.factorization p : Real) / (b : Real) =
          (1 / (b : Real)) * (b.factorization p : Real) := by ring
      _ ≤ (2 / (X : Real)) * (b.factorization p : Real) :=
        mul_le_mul_of_nonneg_right hrecip (Nat.cast_nonneg _)
  calc
    (∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real) / (b : Real)) ≤
      ∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (2 / (X : Real)) * (b.factorization p : Real) :=
      Finset.sum_le_sum hpoint
    _ = (2 / (X : Real)) *
        (∑ b ∈ Finset.Ioc (X / 2) (2 * X),
          (b.factorization p : Real)) := by rw [Finset.mul_sum]
    _ ≤ (2 / (X : Real)) * (4 * (X : Real) / (p : Real)) :=
      mul_le_mul_of_nonneg_left
        (sum_factorization_cutoffBand_le_four_mul_div_prime hp hX)
        (by positivity)
    _ = 8 / (p : Real) := by
      field_simp [hXReal.ne', hpReal.ne']; ring

/-- A pointwise `A/b+E` error on the single cutoff band therefore costs
`8A/p+4EX/p`, including every endpoint `+1`. -/
theorem abs_sum_factorization_mul_cutoffBand_error_le
    {p X : Nat} {error : Nat → Real} {A E : Real}
    (hp : p.Prime) (hX : 1 ≤ X) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (herror : ∀ b ∈ Finset.Ioc (X / 2) (2 * X),
      |error b| ≤ A / (b : Real) + E) :
    |∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real) * error b| ≤
      A * (8 / (p : Real)) +
        E * (4 * (X : Real) / (p : Real)) := by
  have hweighted :=
    weightedFactorizationSum_cutoffBand_le_eight_div_prime hp hX
  have hunweighted :=
    sum_factorization_cutoffBand_le_four_mul_div_prime hp hX
  calc
    |∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real) * error b| ≤
      ∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        |(b.factorization p : Real) * error b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real) * |error b| := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real) * (A / (b : Real) + E) := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (herror b hb) (Nat.cast_nonneg _)
    _ = A * (∑ b ∈ Finset.Ioc (X / 2) (2 * X),
          (b.factorization p : Real) / (b : Real)) +
        E * (∑ b ∈ Finset.Ioc (X / 2) (2 * X),
          (b.factorization p : Real)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ ≤ A * (8 / (p : Real)) +
        E * (4 * (X : Real) / (p : Real)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hweighted hA)
        (mul_le_mul_of_nonneg_left hunweighted hE)

/-! ## The isolated four-to-five chamber input -/





/-- Deep prefix and cutoff band are disjoint. -/
theorem roughCanonicalExceptionalDeepCoreSet_disjoint_cutoffCoreSet
    (deltaStar : Real) (n : Nat) :
    Disjoint (roughCanonicalExceptionalDeepCoreSet deltaStar n)
      (roughCanonicalExceptionalCutoffCoreSet deltaStar n) := by
  rw [Finset.disjoint_left]
  intro b hbDeep hbBand
  simp only [roughCanonicalExceptionalDeepCoreSet,
    roughCanonicalExceptionalCutoffCoreSet, Finset.mem_Icc,
    Finset.mem_Ioc] at hbDeep hbBand
  omega

/-- Deep prefix and cutoff band exhaust the common core prefix. -/
theorem roughCanonicalExceptionalDeepCoreSet_union_cutoffCoreSet
    (deltaStar : Real) (n : Nat) :
    roughCanonicalExceptionalDeepCoreSet deltaStar n ∪
        roughCanonicalExceptionalCutoffCoreSet deltaStar n =
      Finset.Icc 1 (2 * tangentPaperExceptionalCutoff deltaStar n) := by
  ext b
  simp only [roughCanonicalExceptionalDeepCoreSet,
    roughCanonicalExceptionalCutoffCoreSet, Finset.mem_union,
    Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- Exact split of an arbitrary common-prefix sum into the paper's deep
range and its single cutoff band. -/
theorem sum_exceptionalCorePrefix_eq_deep_add_cutoff
    (deltaStar : Real) (n : Nat) (F : Nat → Real) :
    (∑ b ∈ Finset.Icc 1
        (2 * tangentPaperExceptionalCutoff deltaStar n), F b) =
      (∑ b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n, F b) +
        ∑ b ∈ roughCanonicalExceptionalCutoffCoreSet deltaStar n, F b := by
  rw [← Finset.sum_union
    (roughCanonicalExceptionalDeepCoreSet_disjoint_cutoffCoreSet
      deltaStar n),
    roughCanonicalExceptionalDeepCoreSet_union_cutoffCoreSet]



/-- Finite conclusion of the complete core-first argument.  Its right-hand
side displays separately the periodic leading term, the deep chamber error,
the deep endpoint allowance, the cutoff-band error, and the cutoff endpoint
allowance. -/
theorem abs_roughCanonicalSignedExceptionalResidual_le_coreFirstFinite
    {W n h K p : Nat} {deltaStar : Real} {rawWeight : Nat → Real}
    {kernelWeight coreError : Nat → Real}
    {deepConstant cutoffConstant variationConstant : Real}
    (hdelta : 0 ≤ deltaStar) (hn : 1 ≤ n) (hh : h ≤ n)
    (hp : p.Prime) (hWp : W < p) (hpY : p ≤ yNat n)
    (hcut : 2 ≤ tangentPaperExceptionalCutoff deltaStar n)
    (hdeepConstant : 0 ≤ deepConstant)
    (hcutoffConstant : 0 ≤ cutoffConstant)
    (hvariationConstant : 0 ≤ variationConstant)
    (hchamber : RoughCanonicalSignedExceptionalCoreChamberEstimate
      W n h K deltaStar rawWeight kernelWeight coreError
        deepConstant cutoffConstant variationConstant) :
    |roughCanonicalSignedExceptionalResidual n h K deltaStar rawWeight p| ≤
      ((h : Real) / Real.log (yNat n : Real)) *
          (2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
            variationConstant / (p : Real)) +
        (deepConstant * (n : Real) / L n ^ 3) *
          (2 * (1 + Real.log
            ((tangentPaperExceptionalCutoff deltaStar n / 2 : Nat) : Real)) /
              (p : Real)) +
        deepConstant *
          (2 * ((tangentPaperExceptionalCutoff deltaStar n / 2 : Nat) : Real) /
            (p : Real)) +
        (cutoffConstant * (n : Real) / L n ^ 2) *
          (8 / (p : Real)) +
        cutoffConstant *
          (4 * (tangentPaperExceptionalCutoff deltaStar n : Real) /
            (p : Real)) := by
  let X := tangentPaperExceptionalCutoff deltaStar n
  let B := X / 2
  have hB : 1 ≤ B := by omega
  have hX : 1 ≤ X := by omega
  have hlogYPos : 0 < Real.log (yNat n : Real) := by
    have hyTwo : 2 ≤ yNat n := hp.two_le.trans hpY
    exact Real.log_pos (by exact_mod_cast hyTwo)
  have hnTwo : 1 < n := by
    by_contra hnot
    have hnEq : n = 1 := by omega
    subst n
    norm_num [yNat, y] at hpY
    have hpTwo : 2 ≤ p := hp.two_le
    omega
  have hLPos : 0 < L n := L_pos hnTwo
  have hleadNonneg : 0 ≤ (h : Real) / Real.log (yNat n : Real) := by
    positivity
  obtain ⟨hdeep, hdeepError, hband, hvariation⟩ := hchamber
  have hperiodic := abs_roughHeadPeriodicValuationCoreSum_le
    hp hWp hvariationConstant (hvariation p hp hWp)
  have hdeepError' : ∀ b ∈ Finset.Icc 1 B,
      |coreError b| ≤
        (deepConstant * (n : Real) / L n ^ 3) / (b : Real) +
          deepConstant := by
    intro b hb
    have hbDeep : b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n := by
      simpa only [roughCanonicalExceptionalDeepCoreSet, B, X] using hb
    calc
      |coreError b| ≤
          deepConstant * ((n : Real) / ((b : Real) * L n ^ 3) + 1) :=
        hdeepError b hbDeep
      _ = (deepConstant * (n : Real) / L n ^ 3) / (b : Real) +
          deepConstant := by ring
  have hdeepLedger := abs_sum_factorization_mul_error_le
    hp hB (by positivity : 0 ≤ deepConstant * (n : Real) / L n ^ 3)
      hdeepConstant hdeepError'
  have hband' : ∀ b ∈ Finset.Ioc (X / 2) (2 * X),
      |roughCanonicalSignedExceptionalCoreMass n h K deltaStar rawWeight b| ≤
        (cutoffConstant * (n : Real) / L n ^ 2) / (b : Real) +
          cutoffConstant := by
    intro b hb
    have hbBand : b ∈ roughCanonicalExceptionalCutoffCoreSet deltaStar n := by
      simpa only [roughCanonicalExceptionalCutoffCoreSet, X] using hb
    calc
      |roughCanonicalSignedExceptionalCoreMass n h K deltaStar rawWeight b| ≤
          cutoffConstant *
            ((n : Real) / ((b : Real) * L n ^ 2) + 1) := hband b hbBand
      _ = (cutoffConstant * (n : Real) / L n ^ 2) / (b : Real) +
          cutoffConstant := by ring
  have hbandLedger := abs_sum_factorization_mul_cutoffBand_error_le
    hp hX (by positivity : 0 ≤ cutoffConstant * (n : Real) / L n ^ 2)
      hcutoffConstant hband'
  have hdeepIdentity :
      (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : Real) *
          roughCanonicalSignedExceptionalCoreMass
            n h K deltaStar rawWeight b) =
        ((h : Real) / Real.log (yNat n : Real)) *
            roughHeadPeriodicValuationCoreSum W p kernelWeight B +
          ∑ b ∈ Finset.Icc 1 B,
            (b.factorization p : Real) * coreError b := by
    unfold roughHeadPeriodicValuationCoreSum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    have hbDeep : b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n := by
      simpa only [roughCanonicalExceptionalDeepCoreSet, B, X] using hb
    rw [hdeep b hbDeep]
    ring
  rw [roughCanonicalSignedExceptionalResidual_eq_coreFirst
    hdelta hn hh hpY,
    sum_exceptionalCorePrefix_eq_deep_add_cutoff]
  change
    |(∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : Real) *
          roughCanonicalSignedExceptionalCoreMass
            n h K deltaStar rawWeight b) +
      ∑ b ∈ Finset.Ioc (X / 2) (2 * X),
        (b.factorization p : Real) *
          roughCanonicalSignedExceptionalCoreMass
            n h K deltaStar rawWeight b| ≤ _
  rw [hdeepIdentity]
  have hleadLedger :
      |((h : Real) / Real.log (yNat n : Real)) *
          roughHeadPeriodicValuationCoreSum W p kernelWeight B| ≤
        ((h : Real) / Real.log (yNat n : Real)) *
          (2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
            variationConstant / (p : Real)) := by
    rw [abs_mul, abs_of_nonneg hleadNonneg]
    exact mul_le_mul_of_nonneg_left hperiodic hleadNonneg
  calc
    |((h : Real) / Real.log (yNat n : Real)) *
          roughHeadPeriodicValuationCoreSum W p kernelWeight B +
        (∑ b ∈ Finset.Icc 1 B,
          (b.factorization p : Real) * coreError b) +
        ∑ b ∈ Finset.Ioc (X / 2) (2 * X),
          (b.factorization p : Real) *
            roughCanonicalSignedExceptionalCoreMass
              n h K deltaStar rawWeight b| ≤
      |((h : Real) / Real.log (yNat n : Real)) *
          roughHeadPeriodicValuationCoreSum W p kernelWeight B| +
        |∑ b ∈ Finset.Icc 1 B,
          (b.factorization p : Real) * coreError b| +
        |∑ b ∈ Finset.Ioc (X / 2) (2 * X),
          (b.factorization p : Real) *
            roughCanonicalSignedExceptionalCoreMass
              n h K deltaStar rawWeight b| := by
      exact (abs_add_le _ _).trans
        (add_le_add_left (abs_add_le _ _) _)
    _ ≤ ((h : Real) / Real.log (yNat n : Real)) *
          (2 * ((roughHeadModulus W : Real) / roughHeadDensity W) *
            variationConstant / (p : Real)) +
        ((deepConstant * (n : Real) / L n ^ 3) *
          (2 * (1 + Real.log (B : Real)) / (p : Real)) +
        deepConstant * (2 * (B : Real) / (p : Real))) +
        ((cutoffConstant * (n : Real) / L n ^ 2) *
          (8 / (p : Real)) +
        cutoffConstant * (4 * (X : Real) / (p : Real))) := by
      exact add_le_add (add_le_add hleadLedger hdeepLedger) hbandLedger
    _ = _ := by
      simp only [B, X]
      ring

/-! ## Endpoint absorption at the strict paper scale -/









/-! ## Uniform paper-scale packaging -/









end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {W n h K p : Nat} {deltaStar : Real} {rawWeight kernelWeight coreError : Nat → Real}
  {deepConstant cutoffConstant variationConstant : Real},
  LE.le.{0} (0 : Real) deltaStar →
    LE.le.{0} (1 : Nat) n →
      LE.le.{0} h n →
        Nat.Prime p →
          LT.lt.{0} W p →
            LE.le.{0} p (Erdos390.Full.ArithmeticModel.yNat n) →
              LE.le.{0} (2 : Nat) (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n) →
                LE.le.{0} (0 : Real) deepConstant →
                  LE.le.{0} (0 : Real) cutoffConstant →
                    LE.le.{0} (0 : Real) variationConstant →
                      Erdos390.WholePaper.BankPaperRealization.RoughCanonicalSignedExceptionalCoreChamberEstimate W n h
                          K deltaStar rawWeight kernelWeight coreError deepConstant cutoffConstant variationConstant →
                        LE.le.{0}
                          (abs.{0}
                            (Erdos390.WholePaper.BankPaperRealization.roughCanonicalSignedExceptionalResidual n h K
                              deltaStar rawWeight p))
                          (HAdd.hAdd.{0, 0, 0}
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0}
                                    (HDiv.hDiv.{0, 0, 0} (↑h) (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)))
                                    (HDiv.hDiv.{0, 0, 0}
                                      (HMul.hMul.{0, 0, 0}
                                        (HMul.hMul.{0, 0, 0} (2 : Real)
                                          (HDiv.hDiv.{0, 0, 0} (↑(Erdos390.WholePaper.roughHeadModulus W))
                                            (Erdos390.WholePaper.roughHeadDensity W)))
                                        variationConstant)
                                      ↑p))
                                  (HMul.hMul.{0, 0, 0}
                                    (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} deepConstant ↑n)
                                      (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (3 : Nat)))
                                    (HDiv.hDiv.{0, 0, 0}
                                      (HMul.hMul.{0, 0, 0} (2 : Real)
                                        (HAdd.hAdd.{0, 0, 0} (1 : Real)
                                          (Real.log
                                            ↑(HDiv.hDiv.{0, 0, 0}
                                                (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n)
                                                (2 : Nat)))))
                                      ↑p)))
                                (HMul.hMul.{0, 0, 0} deepConstant
                                  (HDiv.hDiv.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0} (2 : Real)
                                      ↑(HDiv.hDiv.{0, 0, 0}
                                          (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n) (2 : Nat)))
                                    ↑p)))
                              (HMul.hMul.{0, 0, 0}
                                (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} cutoffConstant ↑n)
                                  (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat)))
                                (HDiv.hDiv.{0, 0, 0} (8 : Real) ↑p)))
                            (HMul.hMul.{0, 0, 0} cutoffConstant
                              (HDiv.hDiv.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0} (4 : Real)
                                  ↑(Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n))
                                ↑p))) := by
  exact @Erdos390.WholePaper.BankPaperRealization.abs_roughCanonicalSignedExceptionalResidual_le_coreFirstFinite
