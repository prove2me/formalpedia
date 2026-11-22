-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.abs_roughCanonicalRawPrimePowerColumnResidual_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:53:29.471614+00:00
-- url     : https://prove2.me/submissions/24c8ed3c-b539-4124-8c8f-9280bdc51146

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_010

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

/-- Multiplication by `D` gives an exact bijection between coprime
multiples in `(lo,hi]` and reduced residues in `(lo/D,hi/D]`. -/
theorem coprimeMultipleIoc_card_eq_reducedResidueIoc
    {M D lo hi : ℕ} (hD : 0 < D) (hDM : Nat.Coprime D M) :
    (coprimeMultipleIoc M D lo hi).card =
      (reducedResidueIoc M (lo / D) (hi / D)).card := by
  apply Finset.card_bij (fun a _ha ↦ a / D)
  · intro a ha
    simp only [coprimeMultipleIoc, Finset.mem_filter,
      Finset.mem_Ioc] at ha
    obtain ⟨haInterval, hDvd, hcoprime⟩ := ha
    simp only [reducedResidueIoc, Finset.mem_filter,
      Finset.mem_Ioc]
    refine ⟨⟨(Nat.div_lt_iff_lt_mul hD).mpr ?_,
      (Nat.le_div_iff_mul_le hD).mpr ?_⟩, ?_⟩
    · simpa [Nat.div_mul_cancel hDvd] using haInterval.1
    · simpa [Nat.div_mul_cancel hDvd] using haInterval.2
    · rw [← Nat.div_mul_cancel hDvd] at hcoprime
      exact (Nat.coprime_mul_iff_left.mp hcoprime).1
  · intro a₁ ha₁ a₂ ha₂ heq
    simp only [coprimeMultipleIoc, Finset.mem_filter,
      Finset.mem_Ioc] at ha₁ ha₂
    calc
      a₁ = a₁ / D * D := (Nat.div_mul_cancel ha₁.2.1).symm
      _ = a₂ / D * D := by rw [heq]
      _ = a₂ := Nat.div_mul_cancel ha₂.2.1
  · intro b hb
    simp only [reducedResidueIoc, Finset.mem_filter,
      Finset.mem_Ioc] at hb
    refine ⟨b * D, ?_, ?_⟩
    · simp only [coprimeMultipleIoc, Finset.mem_filter,
        Finset.mem_Ioc]
      refine ⟨⟨(Nat.div_lt_iff_lt_mul hD).mp hb.1.1,
        (Nat.le_div_iff_mul_le hD).mp hb.1.2⟩, by simp, ?_⟩
      exact Nat.coprime_mul_iff_left.mpr ⟨hb.2, hDM⟩
    · exact Nat.mul_div_left b hD

/-- Integer quotient lengths differ from real division by less than one.
This is the only extra endpoint cost after the exact multiplication
reindexing. -/
theorem quotientIocLength_sub_realLengthDiv_abs_lt_one
    {D lo hi : ℕ} (hD : 0 < D) (hlohi : lo ≤ hi) :
    |(((hi / D - lo / D : ℕ) : ℝ)) -
        ((hi - lo : ℕ) : ℝ) / (D : ℝ)| < 1 := by
  have hquotient : lo / D ≤ hi / D := Nat.div_le_div_right hlohi
  have hDRealPos : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast hD
  have hDReal : (D : ℝ) ≠ 0 := hDRealPos.ne'
  have hhi := congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.mod_add_div hi D)
  have hlo := congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.mod_add_div lo D)
  simp only [Nat.cast_add, Nat.cast_mul] at hhi hlo
  have herror :
      (((hi / D - lo / D : ℕ) : ℝ)) -
          ((hi - lo : ℕ) : ℝ) / (D : ℝ) =
        ((lo % D : ℕ) : ℝ) / (D : ℝ) -
          ((hi % D : ℕ) : ℝ) / (D : ℝ) := by
    rw [Nat.cast_sub hquotient, Nat.cast_sub hlohi]
    field_simp [hDReal]
    nlinarith [hhi, hlo]
  have hloMod : ((lo % D : ℕ) : ℝ) / (D : ℝ) < 1 := by
    apply (div_lt_one hDRealPos).2
    exact_mod_cast Nat.mod_lt lo hD
  have hhiMod : ((hi % D : ℕ) : ℝ) / (D : ℝ) < 1 := by
    apply (div_lt_one hDRealPos).2
    exact_mod_cast Nat.mod_lt hi hD
  have hloModNonneg :
      0 ≤ ((lo % D : ℕ) : ℝ) / (D : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hDRealPos.le
  have hhiModNonneg :
      0 ≤ ((hi % D : ℕ) : ℝ) / (D : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hDRealPos.le
  rw [herror, abs_lt]
  constructor <;> linarith

/-- CRT-style interval count with an explicit error independent of `D`:
for `D` coprime to `M`, the error is at most `M+1`. -/
theorem coprimeMultipleIoc_card_error_le
    {M D lo hi : ℕ} (hM : 0 < M) (hD : 0 < D)
    (hDM : Nat.Coprime D M) (hlohi : lo ≤ hi) :
    |((coprimeMultipleIoc M D lo hi).card : ℝ) -
        fixedModulusReducedResidueDensity M *
          (((hi - lo : ℕ) : ℝ) / (D : ℝ))| ≤
      (M : ℝ) + 1 := by
  rw [coprimeMultipleIoc_card_eq_reducedResidueIoc hD hDM]
  have hquotient : lo / D ≤ hi / D := Nat.div_le_div_right hlohi
  let quotientLength := hi / D - lo / D
  have hresidue := reducedResidueIoc_card_error_le_modulus
    hM hquotient
  have hresidue' :
      |((reducedResidueIoc M (lo / D) (hi / D)).card : ℝ) -
          fixedModulusReducedResidueDensity M *
            (quotientLength : ℝ)| ≤ (M : ℝ) := by
    simpa only [quotientLength] using hresidue
  have hfloor := quotientIocLength_sub_realLengthDiv_abs_lt_one hD hlohi
  have hMRealPos : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast hM
  have htotientLe : (M.totient : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast Nat.totient_le M
  have hdensityNonneg :
      0 ≤ fixedModulusReducedResidueDensity M :=
    div_nonneg (Nat.cast_nonneg _) hMRealPos.le
  have hdensityLeOne :
      fixedModulusReducedResidueDensity M ≤ 1 := by
    rw [fixedModulusReducedResidueDensity]
    exact (div_le_one hMRealPos).2 htotientLe
  have hscale :
      |fixedModulusReducedResidueDensity M *
          ((quotientLength : ℝ) -
            ((hi - lo : ℕ) : ℝ) / (D : ℝ))| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hdensityNonneg]
    calc
      fixedModulusReducedResidueDensity M *
          |(quotientLength : ℝ) -
            ((hi - lo : ℕ) : ℝ) / (D : ℝ)| ≤
          1 * 1 :=
        mul_le_mul hdensityLeOne
          (by simpa only [quotientLength] using hfloor.le)
          (abs_nonneg _) zero_le_one
      _ = 1 := mul_one _
  have hsplit :
      ((reducedResidueIoc M (lo / D) (hi / D)).card : ℝ) -
          fixedModulusReducedResidueDensity M *
            (((hi - lo : ℕ) : ℝ) / (D : ℝ)) =
        (((reducedResidueIoc M (lo / D) (hi / D)).card : ℝ) -
          fixedModulusReducedResidueDensity M *
            (quotientLength : ℝ)) +
        fixedModulusReducedResidueDensity M *
          ((quotientLength : ℝ) -
            ((hi - lo : ℕ) : ℝ) / (D : ℝ)) := by
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hresidue' hscale)

/-! ## Paper-head specializations -/



/-- The exact `O_W(1)` CRT estimate used for `p^k` multiples in Section 6
and fixed-head multiplier lists in Section 9. -/
theorem roughHeadCoprimeMultipleIoc_card_error_le
    {W D lo hi : ℕ} (hD : 0 < D)
    (hDHead : Nat.Coprime D (roughHeadModulus W))
    (hlohi : lo ≤ hi) :
    |((coprimeMultipleIoc (roughHeadModulus W) D lo hi).card : ℝ) -
        roughHeadDensity W *
          (((hi - lo : ℕ) : ℝ) / (D : ℝ))| ≤
      (roughHeadModulus W : ℝ) + 1 := by
  simpa only [roughHeadDensity, fixedModulusReducedResidueDensity] using
    coprimeMultipleIoc_card_error_le
      (roughHeadModulus_pos W) hD hDHead hlohi

/-- A prime strictly above the cutoff is coprime to the product of every
head prime at or below the cutoff. -/
theorem prime_coprime_roughHeadModulus_of_cutoff_lt
    {W p : ℕ} (hp : p.Prime) (hWp : W < p) :
    Nat.Coprime p (roughHeadModulus W) := by
  rw [roughHeadModulus, Nat.coprime_prod_right_iff]
  intro q hq
  have hqData := mem_primesUpTo.mp hq
  exact (Nat.coprime_primes hp hqData.1).mpr (by omega)

/-- Literal form of the Section 6 estimate
`#{a in I : p^k | a, (a,P_hd)=1} = delta_hd |I|/p^k + O_W(1)`.
The displayed bound `P_hd + 1` is valid for every exponent `k`. -/
theorem roughHeadPrimePowerMultipleIoc_card_error_le
    {W p k lo hi : ℕ} (hp : p.Prime) (hWp : W < p)
    (hlohi : lo ≤ hi) :
    |((coprimeMultipleIoc (roughHeadModulus W) (p ^ k) lo hi).card : ℝ) -
        roughHeadDensity W *
          (((hi - lo : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ))| ≤
      (roughHeadModulus W : ℝ) + 1 := by
  apply roughHeadCoprimeMultipleIoc_card_error_le
  · exact pow_pos hp.pos k
  · exact (prime_coprime_roughHeadModulus_of_cutoff_lt hp hWp).pow_left k
  · exact hlohi

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalBalancedRawSignedValuationResidualBoundConnector -/
section


/-!
# The balanced raw signed valuation residual

The raw signed residual is the one generic term left as a premise in the
four-term paper-rate closure.  This file proves it directly from the
elementary fixed-modulus interval count.

For a fixed prime `p`, every valuation is expanded into the indicators of
`p ^ k` divisibility.  At one exponent, the upper interval has endpoint
error less than one, while each of the two head-free lower intervals has
error at most `roughHeadModulus W + 1`.  The three real-length main terms
cancel exactly by `roughHeadBalancedAlpha_length_normalization`.

The resulting finite bound is logarithmic in the physical endpoint.  The
last section absorbs that logarithm uniformly for `p <= yNat n` into the
paper scale `secondOrderScale n / (p * L n)`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Valuations as finite prime-power column sums -/









/-! ## The literal one-column residual -/

/-- The number of multiples of `D` in `(lo,hi]` differs from the real
interval length divided by `D` by less than one. -/
theorem Ioc_filter_dvd_card_sub_realLengthDiv_abs_lt_one
    {D lo hi : Nat} (hD : 0 < D) (hlohi : lo <= hi) :
    abs ((((Finset.Ioc lo hi).filter (fun a => D ∣ a)).card : Real) -
        (((hi - lo : Nat) : Real) / (D : Real))) < 1 := by
  have hcard :
      ((Finset.Ioc lo hi).filter (fun a => D ∣ a)).card =
        hi / D - lo / D := by
    simpa [coprimeMultipleIoc, reducedResidueIoc] using
      (coprimeMultipleIoc_card_eq_reducedResidueIoc
        (M := 1) (D := D) (lo := lo) (hi := hi) hD
        (by simp : Nat.Coprime D 1))
  rw [hcard]
  exact quotientIocLength_sub_realLengthDiv_abs_lt_one hD hlohi







/-- One prime-power column has only the three literal endpoint errors left
after exact balanced main-term cancellation. -/
theorem abs_roughCanonicalRawPrimePowerColumnResidual_le
    {W n h K p k : Nat} {alpha beta ell : Real}
    (hKh : K * h <= n)
    (hnormalization :
      roughHeadDensity W *
          (alpha * ((K * h : Nat) : Real) +
            (beta / ell) * ((n - K * h : Nat) : Real)) =
        (h : Real))
    (hp : p.Prime) (hWp : W < p) :
    abs (roughCanonicalRawPrimePowerColumnResidual
      W n h K alpha beta ell p k) <=
      1 +
        abs alpha * ((roughHeadModulus W : Real) + 1) +
        abs (beta / ell) * ((roughHeadModulus W : Real) + 1) := by
  let D : Nat := p ^ k
  let U : Real :=
    (((roughUpperBlock n h).filter (fun a => p ^ k ∣ a)).card : Real)
  let H : Real :=
    ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
      (2 * n - K * h) (2 * n)).card : Real)
  let J : Real :=
    ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
      n (2 * n - K * h)).card : Real)
  let delta : Real := roughHeadDensity W
  let q : Real := beta / ell
  have hD : 0 < D := by
    exact pow_pos hp.pos k
  have hDReal : (0 : Real) < (D : Real) := by
    exact_mod_cast hD
  have hupperLength : 2 * n + h - 2 * n = h := by omega
  have hhighLength :
      2 * n - (2 * n - K * h) = K * h := by omega
  have hbroadLength :
      2 * n - K * h - n = n - K * h := by omega
  have hupper :
      abs (U - (h : Real) / (D : Real)) <= 1 := by
    dsimp only [U, D]
    simpa only [roughUpperBlock, hupperLength] using
      (Ioc_filter_dvd_card_sub_realLengthDiv_abs_lt_one
        (D := p ^ k) (lo := 2 * n) (hi := 2 * n + h)
        hD (by omega)).le
  have hhigh :
      abs (H - delta * ((K * h : Nat) : Real) / (D : Real)) <=
        (roughHeadModulus W : Real) + 1 := by
    dsimp only [H, delta, D]
    simpa only [hhighLength, mul_div_assoc] using
      (roughHeadPrimePowerMultipleIoc_card_error_le
        (W := W) (p := p) (k := k)
        (lo := 2 * n - K * h) (hi := 2 * n)
        hp hWp (by omega))
  have hbroad :
      abs (J - delta * ((n - K * h : Nat) : Real) / (D : Real)) <=
        (roughHeadModulus W : Real) + 1 := by
    dsimp only [J, delta, D]
    simpa only [hbroadLength, mul_div_assoc] using
      (roughHeadPrimePowerMultipleIoc_card_error_le
        (W := W) (p := p) (k := k)
        (lo := n) (hi := 2 * n - K * h)
        hp hWp (by omega))
  have hnormalization' :
      delta *
          (alpha * ((K * h : Nat) : Real) +
            q * ((n - K * h : Nat) : Real)) =
        (h : Real) := by
    simpa only [delta, q] using hnormalization
  have hsplit :
      U - alpha * H - q * J =
        (U - (h : Real) / (D : Real)) -
          alpha *
            (H - delta * ((K * h : Nat) : Real) / (D : Real)) -
          q *
            (J - delta * ((n - K * h : Nat) : Real) / (D : Real)) := by
    rw [← hnormalization']
    field_simp [hDReal.ne']
    ring
  unfold roughCanonicalRawPrimePowerColumnResidual
  change abs (U - alpha * H - q * J) <= _
  rw [hsplit]
  calc
    abs ((U - (h : Real) / (D : Real)) -
        alpha *
          (H - delta * ((K * h : Nat) : Real) / (D : Real)) -
        q *
          (J - delta * ((n - K * h : Nat) : Real) / (D : Real))) <=
      abs ((U - (h : Real) / (D : Real)) -
        alpha *
          (H - delta * ((K * h : Nat) : Real) / (D : Real))) +
      abs (q *
        (J - delta * ((n - K * h : Nat) : Real) / (D : Real))) :=
        abs_sub _ _
    _ <=
      (abs (U - (h : Real) / (D : Real)) +
        abs (alpha *
          (H - delta * ((K * h : Nat) : Real) / (D : Real)))) +
      abs (q *
        (J - delta * ((n - K * h : Nat) : Real) / (D : Real))) := by
      exact add_le_add
        (abs_sub
          (U - (h : Real) / (D : Real))
          (alpha *
            (H - delta * ((K * h : Nat) : Real) / (D : Real))))
        (le_refl (abs (q *
          (J - delta * ((n - K * h : Nat) : Real) / (D : Real)))))
    _ =
      abs (U - (h : Real) / (D : Real)) +
        abs alpha *
          abs (H - delta * ((K * h : Nat) : Real) / (D : Real)) +
        abs q *
          abs (J - delta * ((n - K * h : Nat) : Real) / (D : Real)) := by
      rw [abs_mul, abs_mul]
    _ <=
      1 +
        abs alpha * ((roughHeadModulus W : Real) + 1) +
        abs q * ((roughHeadModulus W : Real) + 1) := by
      gcongr
    _ =
      1 +
        abs alpha * ((roughHeadModulus W : Real) + 1) +
        abs (beta / ell) * ((roughHeadModulus W : Real) + 1) := by
      rfl



/-! ## Fixed constants for the balanced point -/













/-! ## Eventual paper-rate absorption -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {W n h K p k : Nat} {alpha beta ell : Real},
  LE.le.{0} (HMul.hMul.{0, 0, 0} K h) n →
    Eq.{1}
        (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.roughHeadDensity W)
          (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} alpha ↑(HMul.hMul.{0, 0, 0} K h))
            (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} beta ell) ↑(HSub.hSub.{0, 0, 0} n (HMul.hMul.{0, 0, 0} K h)))))
        ↑h →
      Nat.Prime p →
        LT.lt.{0} W p →
          LE.le.{0}
            (abs.{0}
              (Erdos390.WholePaper.BankPaperRealization.roughCanonicalRawPrimePowerColumnResidual W n h K alpha beta ell
                p k))
            (HAdd.hAdd.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0} (1 : Real)
                (HMul.hMul.{0, 0, 0} (abs.{0} alpha)
                  (HAdd.hAdd.{0, 0, 0} ↑(Erdos390.WholePaper.roughHeadModulus W) (1 : Real))))
              (HMul.hMul.{0, 0, 0} (abs.{0} (HDiv.hDiv.{0, 0, 0} beta ell))
                (HAdd.hAdd.{0, 0, 0} ↑(Erdos390.WholePaper.roughHeadModulus W) (1 : Real)))) := by
  exact @Erdos390.WholePaper.BankPaperRealization.abs_roughCanonicalRawPrimePowerColumnResidual_le
