-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.abs_roughCanonicalAggregateGuardResidual_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:13:12.291913+00:00
-- url     : https://prove2.me/submissions/b3e7caf2-2272-4b7d-9b47-a26fce58b6aa

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
import Definitions.Def_erdos390_analytic_foundations_009

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













/-- The upper tail is disjoint from every raw lower candidate. -/
theorem roughUpperBlock_disjoint_rawCandidateSet
    (n h K : ℕ) :
    Disjoint (roughUpperBlock n h) (roughRawCandidateSet n h K) := by
  rw [Finset.disjoint_left]
  intro a haUpper haLower
  simp only [roughUpperBlock, roughRawCandidateSet,
    roughHighLowerBlock, roughBroadLowerBlock, Finset.mem_Ioc,
    Finset.mem_union] at haUpper haLower
  rcases haLower with haHigh | haBroad <;> omega







/-! ## The finite head and raw weights -/

















































/-! ## Exact head inclusion--exclusion and smooth physical shifts -/

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomMarkerPools -/
section


/-!
# Literal marker pools for the four bottom bank moves

The four rows below are the natural-number half-open intervals appearing in
the paper.  Each is split at its integer midpoint into two fixed one-half
orientation subintervals.  This file proves only exact finite interval and
factor arithmetic; prime supply is deliberately kept separate.
-/

namespace Erdos390.WholePaper

noncomputable section











































/-- A marker in its row makes both endpoint states and the donor lie in
the factor interval `(n,M]`. -/
theorem bankBottom_states_donor_mem_factorInterval
    {n M marker : ℕ} {move : BankBottomMove}
    (hmarker : marker ∈ bankBottomMarkerInterval n M move) :
    bankBottomLowerState move marker ∈ factorInterval n M ∧
      bankBottomUpperState move marker ∈ factorInterval n M ∧
      bankBottomDonor move marker ∈ factorInterval n M := by
  cases move <;>
    simp only [bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc, bankBottomLowerState,
      bankBottomUpperState, bankBottomDonor,
      bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
      bankBottomDonorMultiplier, factorInterval] at hmarker ⊢ <;>
    omega



















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomPaperComponents -/
section


/-!
# Actual bottom-bank components from the concrete marker matching

The capacity argument deliberately matches the rectangular upper-bound family
consisting of every signed slot and all four bottom rows.  The path belonging
to a small source prime does not use every one of those rows: source `3` uses
only `3→2→1`, and source `2` uses only `2→1`.  This file therefore separates
the full matched family from the literal relevant subfamily before forming any
set of used occurrences.

For every matched request we retain its actual prime marker, the two state
factors in the corresponding row, and its donor occurrence.  A finite set of
occurrence values is used, so in the last two rows the donor and the upper
state are literally one occurrence, rather than two tagged copies.  The only
global input is the already constructed injective marker matching.  All other
claims below are explicit interval, factorization, and large-prime arithmetic.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal relevant subfamily -/





















































/-! ## The deterministic truncated bottom path -/

























/-! ## A realization obtained from the actual matching -/





namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)





















/-- Both row endpoints and the donor are actual factors in `(n,M]`. -/
theorem states_donor_mem_factorInterval (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    realization.lowerStateFactor request ∈ factorInterval n M ∧
      realization.upperStateFactor request ∈ factorInterval n M ∧
      realization.donorFactor request ∈ factorInterval n M := by
  simpa only [lowerStateFactor, upperStateFactor, donorFactor] using
    bankBottom_states_donor_mem_factorInterval
      (realization.marker_mem_row hTwoN request)







/-! The four paper rows, with the marker made explicit. -/













/-! ## Orientation-aware realized row and slot changes -/























end BankBottomPaperRealization

/-! ## Complete occurrence sets and rough signatures -/









namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)





























theorem componentOccurrence_mem_factorInterval
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈ realization.componentOccurrences request) :
    occurrence ∈ factorInterval n M := by
  rw [realization.componentOccurrences_eq_states_insert_donor request]
    at hoccurrence
  simp only [Finset.mem_insert, Finset.mem_singleton] at hoccurrence
  have hinterval := realization.states_donor_mem_factorInterval hTwoN request
  rcases hoccurrence with hoccurrence | hoccurrence | hoccurrence
  · simpa only [hoccurrence] using hinterval.1
  · simpa only [hoccurrence] using hinterval.2.1
  · simpa only [hoccurrence] using hinterval.2.2

























end BankBottomPaperRealization

/-! ## Explicit local geometry and collision freedom -/



namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)









/-! ## Relevant markers and marker-to-component uniqueness -/



























end BankBottomPaperRealization

/-! ## Cardinality bound for the actual relevant marker set -/

theorem card_bankBottomPaperRequests (n : ℕ) :
    (bankBottomPaperRequests n).card = 8 * bankBottomPaperDemand n := by
  have hsigned :
      Fintype.card (SignedBankSlot (bankRoundingBetaOnSupport n)) =
        2 * bankBottomPaperDemand n := by
    rw [Fintype.card_sigma]
    change (∑ p : bankRoundingPrimeSupport n,
      Fintype.card (Fin (bankRoundingBeta n p) ⊕ Fin (bankRoundingBeta n p))) = _
    simp only [Fintype.card_sum, Fintype.card_fin]
    calc
      (∑ p : ↑(bankRoundingPrimeSupport n),
          (bankRoundingBeta n p.1 + bankRoundingBeta n p.1)) =
          2 * ∑ p : ↑(bankRoundingPrimeSupport n),
            bankRoundingBeta n p.1 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p _hp
              omega
      _ = 2 * bankBottomPaperDemand n := by
        congr 1
        simpa only [bankBottomPaperDemand] using
          (Finset.sum_attach (bankRoundingPrimeSupport n)
            (fun p ↦ bankRoundingBeta n p))
  rw [bankBottomPaperRequests, Finset.card_univ, Fintype.card_prod,
    hsigned, show Fintype.card BankBottomMove = 4 by decide]
  ring





/-! ## Eventual local geometry and the terminal realized family -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryPaperComponents -/
section


/-!
# Realized ordinary bank components

An ordinary matching supplies an actual pair `(P,u)` to every concrete path
request `q→b`.  This file materializes the three factor occurrences

* source state `P*q`,
* target state `P*b`, and
* backing donor `P*u`.

All three lie in `(n,M]` and have the same complete rough signature.  The
large prime marker is recovered uniquely from any realized occurrence, which
gives marker injectivity, donor-product injectivity, and collision-freedom
across requests, scales, and orientations.  Finally, cancellation of the
common marker turns the realized component changes back into the actual
finite path telescope.

The public names intentionally mirror `BankBottomPaperComponents`: a
realization object, factor-valued methods, an occurrence-kind enumeration,
and `occurrenceValue`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Coarse global size bounds -/













/-! ## Arithmetic helpers for rough signatures -/









/-! ## Marker injectivity inherited from the orientation pools -/









/-! ## The public realization object and its actual factors -/



namespace BankOrdinaryPaperRealization



































private theorem stateValues_mem_factorInterval
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.sourceStateValue request ∈ factorInterval n M ∧
      R.targetStateValue request ∈ factorInterval n M := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  have hspec := bankOrdinaryPaperRequest_component_spec request.1
  let P := R.marker request
  let q := bankOrdinaryPaperRequestSource request.1
  let b := bankOrdinaryPaperRequestTarget request.1
  let Q := bankOrdinaryScale
    (bankOrdinaryPaperRequestPool n request.1).1
  have hPpos : (0 : ℚ) < P := by
    exact_mod_cast (R.marker_prime request).pos
  have hPnonneg : (0 : ℚ) ≤ P := hPpos.le
  have hmarker := heligible.2.2.2.1
  have hcell := hspec.2.2.2.2.2.2
  change 4 * (n : ℚ) < 3 * Q * P ∧
    2 * Q * P ≤ 3 * (n : ℚ) at hmarker
  change (Q < (q : ℚ) ∧ (q : ℚ) ≤ 4 * Q / 3) ∧
    3 * Q / 4 < (b : ℚ) at hcell
  have hQq := mul_lt_mul_of_pos_left hcell.1.1
    hPpos
  have hqUpper := mul_le_mul_of_nonneg_left hcell.1.2 hPnonneg
  have hbLower := mul_lt_mul_of_pos_left hcell.2
    hPpos
  have hmarkerLower := hmarker.1
  have hmarkerUpper := hmarker.2
  have hsourceLowerQ : (n : ℚ) < P * q := by
    nlinarith [hmarkerLower, hQq]
  have htargetLowerQ : (n : ℚ) < P * b := by
    nlinarith [hmarkerLower, hbLower]
  have hcellSourceUpper : P * (4 * Q / 3) ≤ 2 * (n : ℚ) := by
    have hscaled := mul_le_mul_of_nonneg_left hmarkerUpper
      (by norm_num : (0 : ℚ) ≤ 2 / 3)
    convert hscaled using 1 <;> ring
  have hsourceUpperQ : P * q ≤ 2 * (n : ℚ) := by
    exact hqUpper.trans hcellSourceUpper
  have hsourceLower : n < P * q := by exact_mod_cast hsourceLowerQ
  have htargetLower : n < P * b := by exact_mod_cast htargetLowerQ
  have hsourceUpper : P * q ≤ M := by
    have : P * q ≤ 2 * n := by exact_mod_cast hsourceUpperQ
    exact this.trans R.two_mul_n_le_M
  have htargetUpper : P * b ≤ M := by
    have hbq : b ≤ q := hspec.2.2.2.2.1.le
    exact (Nat.mul_le_mul_left P hbq).trans hsourceUpper
  simp only [sourceStateValue, targetStateValue, factorInterval,
    Finset.mem_Ioc]
  exact ⟨⟨hsourceLower, hsourceUpper⟩,
    ⟨htargetLower, htargetUpper⟩⟩

theorem donorValue_mem_factorInterval
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.donorValue request ∈ factorInterval n M := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  simp only [donorValue, factorInterval, Finset.mem_Ioc]
  have hlower := heligible.2.2.2.2.2.2.1
  change 2 * n < R.marker request * R.donorCore request at hlower
  exact ⟨by omega, heligible.2.2.2.2.2.2.2⟩





































/-! ## The three actual occurrences and global collision-freedom -/





theorem two_mul_n_lt_donorValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    2 * n < R.donorValue request :=
  (mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)).2.2.2.2.2.2.1



























theorem componentOccurrence_mem_factorInterval
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈ R.componentOccurrences request) :
    occurrence ∈ factorInterval n M := by
  rw [componentOccurrences, Finset.mem_image] at hoccurrence
  obtain ⟨kind, _hkind, hvalue⟩ := hoccurrence
  cases kind
  · simpa only [← hvalue, occurrenceValue_sourceState] using
      (R.stateValues_mem_factorInterval request).1
  · simpa only [← hvalue, occurrenceValue_targetState] using
      (R.stateValues_mem_factorInterval request).2
  · simpa only [← hvalue, occurrenceValue_donor] using
      R.donorValue_mem_factorInterval request





/-! ## Realized component and signed-slot changes -/























end BankOrdinaryPaperRealization

/-! ## Eventual realized allocation -/



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





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrecharge -/
section


/-!
# The actual precharged bank state

This module is independent of the eventual path selector.  Its component
index is the already realized global request type: every relevant bottom row
and every ordinary row occurs exactly once.  For each component we expose its
orientation-aware base and alternate states and its actual donor occurrence.

The proofs below use only the explicit component geometry.  In particular,
there is no abstract capacity or compatibility hypothesis: global
injectivity follows from the realized occurrence-set disjointness, and the
donor tail is the literal interval `(2n,M]`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section



namespace BankBottomPaperRealization

/-- Every actual bottom donor is in the strict tail above `2n`. -/
theorem two_mul_n_lt_donorFactor
    {n M : ℕ} (R : BankBottomPaperRealization n M)
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    2 * n < R.donorFactor request := by
  have hrow := R.marker_mem_row hTwoN request
  cases hmove : R.move request <;>
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc, donorFactor,
      bankBottomDonor, bankBottomDonorMultiplier] at hrow ⊢ <;> omega

end BankBottomPaperRealization

namespace BankPaperRealization

attribute [local instance] Erdos390.WholePaper.BankPaperRealization.bankPaperMarkerRequestDecidableEq

/-! ## Global component data -/

















/-- Every named occurrence of every component lies in the factor interval. -/
theorem prechargeComponentOccurrence_mem_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) {occurrence : ℕ}
    (hoccurrence : occurrence ∈
      R.prechargeComponentOccurrences request) :
    occurrence ∈ factorInterval n M := by
  cases request with
  | inl request =>
      exact R.bottom.componentOccurrence_mem_factorInterval
        R.ordinary.two_mul_n_le_M
        (bankBottomRelevantRequestToPaperRequest request) hoccurrence
  | inr request =>
      exact R.ordinary.componentOccurrence_mem_factorInterval
        request hoccurrence

theorem prechargeBaseStateValue_mem_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeBaseStateValue request ∈ factorInterval n M :=
  R.prechargeComponentOccurrence_mem_factorInterval request
    (R.prechargeBaseStateValue_mem_componentOccurrences request)

theorem prechargeAlternateStateValue_mem_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeAlternateStateValue request ∈ factorInterval n M :=
  R.prechargeComponentOccurrence_mem_factorInterval request
    (R.prechargeAlternateStateValue_mem_componentOccurrences request)



/-! ## Complete rough signatures -/







/-! ## Endpoint and donor injectivity -/















theorem prechargeAlternateStateValue_injective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective R.prechargeAlternateStateValue := by
  intro request request' heq
  by_contra hrequest
  exact R.prechargeEndpointValue_ne_of_request_ne
    hrequest .alternate .alternate heq





/-! ## Literal finite states, donor tail, and replacement map -/













theorem prechargeBaseState_card
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeBaseState.card =
      Fintype.card (BankPaperMarkerRequest n) := by
  rw [prechargeBaseState, indexedPathState,
    Finset.card_image_of_injective _ R.prechargeBaseStateValue_injective]
  simp

theorem prechargeAlternateState_card
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeAlternateState.card =
      Fintype.card (BankPaperMarkerRequest n) := by
  rw [prechargeAlternateState, indexedPathState,
    Finset.card_image_of_injective _
      R.prechargeAlternateStateValue_injective]
  simp

theorem prechargeDonorSet_card
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeDonorSet.card =
      Fintype.card (BankPaperMarkerRequest n) := by
  rw [prechargeDonorSet, indexedPathState,
    Finset.card_image_of_injective _ R.prechargeDonorValue_injective]
  simp



theorem prechargeBaseState_subset_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeBaseState ⊆ factorInterval n M := by
  intro value hvalue
  rw [prechargeBaseState, indexedPathState, Finset.mem_image] at hvalue
  obtain ⟨request, _hrequest, rfl⟩ := hvalue
  exact R.prechargeBaseStateValue_mem_factorInterval request

theorem prechargeAlternateState_subset_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeAlternateState ⊆ factorInterval n M := by
  intro value hvalue
  rw [prechargeAlternateState, indexedPathState, Finset.mem_image] at hvalue
  obtain ⟨request, _hrequest, rfl⟩ := hvalue
  exact R.prechargeAlternateStateValue_mem_factorInterval request

/-- Every donor, ordinary or bottom, is an actual factor in `(2n,M]`. -/
theorem prechargeDonorValue_mem_tail
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeDonorValue request ∈ Finset.Ioc (2 * n) M := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      have hlower := R.bottom.two_mul_n_lt_donorFactor
        R.ordinary.two_mul_n_le_M fullRequest
      have hupper : R.bottom.donorFactor fullRequest ≤ M := by
        have hdata : n < R.bottom.donorFactor fullRequest ∧
            R.bottom.donorFactor fullRequest ≤ M := by
          simpa only [factorInterval, Finset.mem_Ioc] using
            (R.bottom.states_donor_mem_factorInterval
              R.ordinary.two_mul_n_le_M fullRequest).2.2
        exact hdata.2
      simpa only [prechargeDonorValue, fullRequest,
        Finset.mem_Ioc] using And.intro hlower hupper
  | inr request =>
      have hlower := R.ordinary.two_mul_n_lt_donorValue request
      have hupper : R.ordinary.donorValue request ≤ M := by
        have hdata : n < R.ordinary.donorValue request ∧
            R.ordinary.donorValue request ≤ M := by
          simpa only [factorInterval, Finset.mem_Ioc] using
            (R.ordinary.donorValue_mem_factorInterval request)
        exact hdata.2
      simpa only [prechargeDonorValue, Finset.mem_Ioc] using
        And.intro hlower hupper

theorem prechargeDonorSet_subset_tail
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeDonorSet ⊆ Finset.Ioc (2 * n) M := by
  intro donor hdonor
  rw [prechargeDonorSet, indexedPathState, Finset.mem_image] at hdonor
  obtain ⟨request, _hrequest, rfl⟩ := hdonor
  exact R.prechargeDonorValue_mem_tail request





















/-! ## Component counts and the base product -/



theorem card_bankPaperMarkerRequest (n : ℕ) :
    Fintype.card (BankPaperMarkerRequest n) =
      (bankBottomRelevantPaperRequests n).card +
        (bankOrdinaryPaperRequests n).card := by
  change Fintype.card
      (↑(bankBottomRelevantPaperRequests n) ⊕
        ↑(bankOrdinaryPaperRequests n)) = _
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]

/-- The global component index has a realization-independent coarse bound.
The bottom contribution is a filtered subfamily of the full eight-row
request rectangle. -/
theorem card_bankPaperMarkerRequest_le_anchorMarkerBudget (n : ℕ) :
    Fintype.card (BankPaperMarkerRequest n) ≤
      bankPaperAnchorMarkerBudget n := by
  rw [card_bankPaperMarkerRequest, bankPaperAnchorMarkerBudget]
  have hbottom : (bankBottomRelevantPaperRequests n).card ≤
      8 * bankBottomPaperDemand n := by
    calc
      (bankBottomRelevantPaperRequests n).card ≤
          (bankBottomPaperRequests n).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 8 * bankBottomPaperDemand n :=
        card_bankBottomPaperRequests n
  omega

theorem prechargeComponentCount_le_anchorMarkerBudget
    {n M : ℕ} (_R : BankPaperRealization n M) :
    Fintype.card (BankPaperMarkerRequest n) ≤
      bankPaperAnchorMarkerBudget n := by
  exact card_bankPaperMarkerRequest_le_anchorMarkerBudget n















end BankPaperRealization

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







namespace BankPaperRealization





theorem paperFixedExceptionalFactors_subset_upperBlock
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆ roughUpperBlock n h := by
  intro a ha
  rw [paperFixedExceptionalFactors, Finset.mem_sdiff] at ha
  exact (mem_paperExceptionalUpperFactors.mp ha.1).1





















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentPaperNumericalGuards -/
section


/-!
# The literal Section 9 numerical guards and bank-row census

This file instantiates the exhaustive numerical guard family used by the
tangent common lists.  In the notation of the paper it is exactly

`Γ_num = H' ∪ G_fix ∪ E_donor ∪ G_bank^0 ∪ G_bank^1`.

Here `H'` is the actual guarded central-anchor set, `G_fix` is supplied by
the eventual rough selector, and the last three sets are the already
constructed precharge donor, base-state, and alternate-state sets.  The
global union is bounded directly from these definitions.  For a permitted
pair `u,v`, its lower-endpoint-relevant subfamily has at most two promoted
anchors and two bank states per component; fixed exceptional factors and
donors disappear because they lie strictly above `2n`.

The paper's bank-row census is also made literal.  The nontrivial bank rows
are the realized marker rows, while the fully dedicated set is empty.  Thus
the dedicated-row deletion in `TangentCommonMultiplierLists` is exactly
zero, without an assumed cardinality estimate.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Actual bank rows and the exhaustive five-family guard set -/





















end BankPaperRealization

/-! ## Only promoted anchors can meet a permitted medium label -/

/-- A prime between the fixed cofactor prefix and the smooth cutoff cannot
divide any routed large-marker anchor. -/
theorem mediumPrime_not_dvd_guardedLargeCentralAnchor
    {c : ℝ} {depth n W y ℓ P : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hPrefix : 2 * depth + 1 ≤ W)
    (hWℓ : W < ℓ) (hℓy : ℓ ≤ y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (hℓPrime : ℓ.Prime)
    (hP : P ∈ largeCentralPrimes n
      (centralAnchorCutoff depth n)) :
    ¬ℓ ∣ largeCentralAnchor certificate.q P := by
  intro hdiv
  rw [largeCentralAnchor] at hdiv
  rcases hℓPrime.dvd_mul.mp hdiv with hℓP | hℓq
  · have hPPrime := largeCentralPrimes_prime hP
    have hEq : ℓ = P :=
      (Nat.prime_dvd_prime_iff_eq hℓPrime hPPrime).mp hℓP
    have hPLarge := largeCentralPrimes_gt hP
    omega
  · have hqPos : 0 < certificate.q P :=
      largeCentralCofactor_pos certificate.isCofactorChoice hP
    have hℓLeQ : ℓ ≤ certificate.q P := Nat.le_of_dvd hqPos hℓq
    have hqLe : certificate.q P ≤ 2 * depth + 1 :=
      largeCentralCofactor_le_fixedPrefix
        certificate.isCofactorChoice hP
    omega

/-- For one permitted pair, every central anchor divisible by `u` or `v`
is one of the two corresponding promoted factors.  The prefix, row-zero,
and other large-marker anchors are eliminated arithmetically. -/
theorem guardedCentralAnchors_pairPrimeDivisors_subset
    {c : ℝ} {depth n W y u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    certificate.anchors.filter (fun g ↦ u ∣ g ∨ v ∣ g) ⊆
      {promotedCentralFactor n u, promotedCentralFactor n v} := by
  intro g hg
  have hgAnchor := (Finset.mem_filter.mp hg).1
  have hgDiv := (Finset.mem_filter.mp hg).2
  rw [certificate.anchors_eq, fullCentralAnchors] at hgAnchor
  rcases Finset.mem_union.mp hgAnchor with hgPromoted | hgLarge
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hgPromoted
    have hpPrime := residualCentralPrimes_prime hp
    rcases hgDiv with huDiv | hvDiv
    · rcases prime_dvd_promotedCentralFactor hpPrime huPrime huDiv with
        huTwo | hup
      · omega
      · subst p
        simp
    · rcases prime_dvd_promotedCentralFactor hpPrime hvPrime hvDiv with
        hvTwo | hvp
      · omega
      · subst p
        simp
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hgLarge
    exfalso
    rcases hgDiv with huDiv | hvDiv
    · exact mediumPrime_not_dvd_guardedLargeCentralAnchor
        certificate hPrefix (hWv.trans_le hvu) huy hyCutoff
          huPrime hP huDiv
    · exact mediumPrime_not_dvd_guardedLargeCentralAnchor
        certificate hPrefix hWv (hvu.trans huy) hyCutoff
          hvPrime hP hvDiv

theorem card_guardedCentralAnchors_pairPrimeDivisors_le_two
    {c : ℝ} {depth n W y u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (certificate.anchors.filter (fun g ↦ u ∣ g ∨ v ∣ g)).card ≤ 2 := by
  have hsubset := guardedCentralAnchors_pairPrimeDivisors_subset
    certificate hTwoW hPrefix hWv hvu huy hyCutoff huPrime hvPrime
  have hcard := Finset.card_le_card hsubset
  have hpair :
      ({promotedCentralFactor n u,
          promotedCentralFactor n v} : Finset ℕ).card ≤ 2 := by
    exact Finset.card_le_two
  omega

namespace BankPaperRealization

/-! ## A lossless endpoint-relevant overapproximation and its upper bound -/









/-! ## Filtering is lossless for actual endpoint deletion -/











/-! ## The actual deterministic common-list ledger -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardLocalRowLedger -/
section


/-!
# Guard-local canonical rough-row ledger

This module isolates the finite bookkeeping that occurs when the paper
passes from the raw canonical rough candidates to the candidates left after
the numerical guards

`Gamma_num = anchors ∪ G_fix ∪ E_donor ∪ G_bank^0 ∪ G_bank^1`.

Only literal finite-set identities are proved here.  In particular, this
file does **not** assume or assert a local guard census, a lower bound for a
guarded broad pool, or enough guarded-row capacity for a corrected selector.
Those still-missing estimates are exposed at the end as named propositions.

The postcharge target is kept in `Real` form for the correction algebra and
in `Int` form for its exact integrality witness.  Its nonnegativity is a
finite consequence of the actual donor/base row-preserving bijection and of
the disjoint upper-tail backing of the fixed exceptional factors and donors.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## Literal guarded candidates and row pieces -/



























/-! ## The donor/base row-preserving bijection -/









/-! ## Upper-tail ownership and the postcharge target -/





























/-! ## Exact local discrepancy ledger -/







/-! ## Exact support reduction for the local deletion set -/

/-- Fixed exceptional factors cannot themselves be raw lower candidates. -/
theorem roughRawCandidateSet_disjoint_paperFixedExceptionalFactors
    {n h K : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    Disjoint (roughRawCandidateSet n h K)
      (R.paperFixedExceptionalFactors deltaStar) := by
  exact (roughUpperBlock_disjoint_rawCandidateSet n h K).symm.mono
    (by rfl) (R.paperFixedExceptionalFactors_subset_upperBlock deltaStar)

/-- Actual donors also lie strictly above every raw lower candidate. -/
theorem roughRawCandidateSet_disjoint_prechargeDonorSet
    {n h K : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h)) :
    Disjoint (roughRawCandidateSet n h K) R.prechargeDonorSet := by
  have hdonor : R.prechargeDonorSet ⊆ roughUpperBlock n h := by
    simpa only [roughUpperBlock, upperEndpoint] using
      R.prechargeDonorSet_subset_tail
  exact (roughUpperBlock_disjoint_rawCandidateSet n h K).symm.mono
    (by rfl) hdonor



/-! ## Explicit remaining finite/analytic obligations -/







end BankPaperRealization

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

/-- A finite family contained in `(lo,hi]` has total `p`-valuation at most
its cardinality times the binary logarithm of `hi`.  The binary logarithm
is deliberately used as a uniform upper bound for every prime base. -/
theorem sum_factorization_cast_le_card_mul_log_two
    {S : Finset Nat} {lo hi p : Nat} (hp : p.Prime)
    (hS : S ⊆ Finset.Ioc lo hi) :
    (∑ a ∈ S, (a.factorization p : Real)) ≤
      (S.card : Real) * (Nat.log 2 hi : Real) := by
  have hNat :
      ∑ a ∈ S, a.factorization p ≤ S.card * Nat.log 2 hi := by
    calc
      ∑ a ∈ S, a.factorization p ≤
          ∑ _a ∈ S, Nat.log 2 hi := by
        apply Finset.sum_le_sum
        intro a ha
        have haIoc := Finset.mem_Ioc.mp (hS ha)
        exact (factorization_le_log_of_pos_le
          (Nat.zero_lt_of_lt haIoc.1) haIoc.2 hp).trans
            (Nat.log_anti_left Nat.one_lt_two hp.two_le)
      _ = S.card * Nat.log 2 hi := by simp
  exact_mod_cast hNat

/-- A feasible nonnegative weight cannot increase a nonnegative valuation
sum.  This is the precise justification used below when a deleted raw
coordinate is replaced by its unweighted valuation. -/
theorem abs_sum_weight_mul_factorization_le_sum_factorization
    {S : Finset Nat} {weight : Nat → Real} {p : Nat}
    (hweight : ∀ a ∈ S, 0 ≤ weight a ∧ weight a ≤ 1) :
    abs (∑ a ∈ S, weight a * (a.factorization p : Real)) ≤
      ∑ a ∈ S, (a.factorization p : Real) := by
  have hsumNonneg :
      0 ≤ ∑ a ∈ S, weight a * (a.factorization p : Real) := by
    apply Finset.sum_nonneg
    intro a ha
    exact mul_nonneg (hweight a ha).1 (Nat.cast_nonneg _)
  rw [abs_of_nonneg hsumNonneg]
  apply Finset.sum_le_sum
  intro a ha
  exact mul_le_of_le_one_left (Nat.cast_nonneg _) (hweight a ha).2

/-- The valuation of a union is no larger than the sum of the valuations
of its two constituent families.  No disjointness is required. -/
theorem sum_factorization_union_le
    (S T : Finset Nat) (p : Nat) :
    (∑ a ∈ S ∪ T, (a.factorization p : Real)) ≤
      (∑ a ∈ S, (a.factorization p : Real)) +
        ∑ a ∈ T, (a.factorization p : Real) := by
  calc
    (∑ a ∈ S ∪ T, (a.factorization p : Real)) =
        ∑ a ∈ S ∪ (T \ S), (a.factorization p : Real) := by
      rw [Finset.union_sdiff_self_eq_union]
    _ = (∑ a ∈ S, (a.factorization p : Real)) +
          ∑ a ∈ T \ S, (a.factorization p : Real) := by
      rw [Finset.sum_union Finset.disjoint_sdiff]
    _ ≤ (∑ a ∈ S, (a.factorization p : Real)) +
          ∑ a ∈ T, (a.factorization p : Real) := by
      have hsdiff :
          (∑ a ∈ T \ S, (a.factorization p : Real)) ≤
            ∑ a ∈ T, (a.factorization p : Real) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun (a : Nat) _ha _hnew ↦
            (Nat.cast_nonneg (a.factorization p) :
              (0 : Real) ≤ (a.factorization p : Real)))
      exact add_le_add le_rfl hsdiff

/-! ## Literal signed exceptional term -/











/-! ## Literal aggregate guard difference -/









/-- The exceptional donors are a literal filtered subfamily of all donors. -/
theorem roughCanonicalExceptionalDonorSet_subset_prechargeDonorSet
    {n h : Nat} (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) :
    R.roughCanonicalExceptionalDonorSet deltaStar ⊆
      R.prechargeDonorSet := by
  classical
  exact Finset.filter_subset _ _

/-- Globally, as rowwise, fixed exceptional factors and donor occurrences
cannot delete raw lower coordinates.  Thus only central anchors and the two
bank endpoint states occur in the first guard-residual sum. -/
theorem roughCanonicalNonexceptionalGuardDeletedSet_subset_support
    {c : Real} {depth n h : Nat} {left right : Nat → Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K : Nat) :
    R.roughCanonicalNonexceptionalGuardDeletedSet certificate deltaStar K ⊆
      certificate.anchors ∪ R.prechargeBaseState ∪
        R.prechargeAlternateState := by
  intro a ha
  have haData :=
    (R.mem_roughCanonicalNonexceptionalGuardDeletedSet certificate
      deltaStar).mp ha
  have haRaw := haData.1
  have haGuard := haData.2.1
  simp only [roughCanonicalGuardSet, tangentPaperNumericalGuardSet,
    Finset.mem_union] at haGuard
  simp only [Finset.mem_union]
  rcases haGuard with (((haAnchor | haFixed) | haDonor) | haBase) | haAlt
  · exact Or.inl (Or.inl haAnchor)
  · exact ((Finset.disjoint_left.mp
      (R.roughRawCandidateSet_disjoint_paperFixedExceptionalFactors
        deltaStar)) haRaw haFixed).elim
  · exact ((Finset.disjoint_left.mp
      (R.roughRawCandidateSet_disjoint_prechargeDonorSet
        (K := K))) haRaw haDonor).elim
  · exact Or.inl (Or.inr haBase)
  · exact Or.inr haAlt



set_option maxHeartbeats 2000000 in
/-- The guard difference is bounded by the absolute values of its three
literal signed components.  This deliberately does not replace the signed
exceptional term by the positive exceptional charge. -/
theorem abs_roughCanonicalAggregateGuardResidual_le_components
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K : Nat) (rawWeight : Nat -> Real)
    (p : Nat) :
    abs (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
      rawWeight p) <=
      abs (∑ a ∈ R.roughCanonicalNonexceptionalGuardDeletedSet certificate
          deltaStar K,
        rawWeight a * (a.factorization p : Real)) +
      abs (∑ a ∈ R.roughCanonicalExceptionalDonorSet deltaStar,
        (a.factorization p : Real)) +
      abs (∑ a ∈ R.prechargeBaseState,
        (a.factorization p : Real)) := by
  unfold roughCanonicalAggregateGuardResidual
  have hadd := abs_add_le
    (∑ a ∈ R.roughCanonicalNonexceptionalGuardDeletedSet certificate
        deltaStar K,
      rawWeight a * (a.factorization p : Real))
    (∑ a ∈ R.roughCanonicalExceptionalDonorSet deltaStar,
      (a.factorization p : Real))
  have hsub := abs_sub
    ((∑ a ∈ R.roughCanonicalNonexceptionalGuardDeletedSet certificate
        deltaStar K,
      rawWeight a * (a.factorization p : Real)) +
      ∑ a ∈ R.roughCanonicalExceptionalDonorSet deltaStar,
        (a.factorization p : Real))
    (∑ a ∈ R.prechargeBaseState, (a.factorization p : Real))
  exact hsub.trans (add_le_add hadd le_rfl)

/-! ## A uniform finite guard-profile bound -/

/-- At a medium prime, only the corresponding promoted central anchors can
carry valuation.  The pair-divisor census, specialized to `(p,p)`, gives a
safe cardinality two, and every anchor is at most `2n`. -/
theorem sum_guardedCentralAnchors_factorization_le_two_mul_log_two
    {c : Real} {depth n W p : Nat} {left right : Nat → Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWp : W < p) (hpY : p ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hp : p.Prime) :
    (∑ a ∈ certificate.anchors, (a.factorization p : Real)) ≤
      2 * (Nat.log 2 (3 * n) : Real) := by
  let divisors := certificate.anchors.filter (fun a ↦ p ∣ a)
  have hsum :
      (∑ a ∈ divisors, (a.factorization p : Real)) =
        ∑ a ∈ certificate.anchors, (a.factorization p : Real) := by
    apply Finset.sum_subset
    · exact Finset.filter_subset _ _
    · intro a haAnchor haNotDivisors
      have hnotDvd : ¬ p ∣ a := by
        intro hpa
        exact haNotDivisors (Finset.mem_filter.mpr ⟨haAnchor, hpa⟩)
      simp [Nat.factorization_eq_zero_of_not_dvd hnotDvd]
  have hcard : divisors.card ≤ 2 := by
    have hpair := card_guardedCentralAnchors_pairPrimeDivisors_le_two
      certificate hTwoW hPrefix hWp (le_refl p) hpY hyCutoff hp hp
    simpa only [divisors, or_self] using hpair
  have hdivisorsSubset : divisors ⊆ Finset.Ioc n (3 * n) := by
    intro a ha
    have haAnchor := (Finset.mem_filter.mp ha).1
    have haIoc := Finset.mem_Ioc.mp (certificate.anchors_subset haAnchor)
    exact Finset.mem_Ioc.mpr ⟨haIoc.1, haIoc.2.trans (by omega)⟩
  calc
    (∑ a ∈ certificate.anchors, (a.factorization p : Real)) =
        ∑ a ∈ divisors, (a.factorization p : Real) := hsum.symm
    _ ≤ (divisors.card : Real) * (Nat.log 2 (3 * n) : Real) :=
      sum_factorization_cast_le_card_mul_log_two hp hdivisorsSubset
    _ ≤ 2 * (Nat.log 2 (3 * n) : Real) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (Nat.cast_nonneg _)

/-- Donor, base, and alternate bank states each have at most the global
marker budget many endpoints, all lying below the realized endpoint. -/
theorem precharge_guard_state_factorization_bounds
    {n M p : Nat} (R : BankPaperRealization n M)
    (hp : p.Prime) (hendpoint : M ≤ 3 * n) :
    ((∑ a ∈ R.prechargeDonorSet, (a.factorization p : Real)) ≤
        (bankPaperAnchorMarkerBudget n : Real) *
          (Nat.log 2 (3 * n) : Real)) ∧
      ((∑ a ∈ R.prechargeBaseState, (a.factorization p : Real)) ≤
        (bankPaperAnchorMarkerBudget n : Real) *
          (Nat.log 2 (3 * n) : Real)) ∧
      ((∑ a ∈ R.prechargeAlternateState,
          (a.factorization p : Real)) ≤
        (bankPaperAnchorMarkerBudget n : Real) *
          (Nat.log 2 (3 * n) : Real)) := by
  have hcomponent : Fintype.card (BankPaperMarkerRequest n) ≤
      bankPaperAnchorMarkerBudget n :=
    R.prechargeComponentCount_le_anchorMarkerBudget
  have hcardScale :
      (Fintype.card (BankPaperMarkerRequest n) : Real) *
          (Nat.log 2 (3 * n) : Real) ≤
        (bankPaperAnchorMarkerBudget n : Real) *
          (Nat.log 2 (3 * n) : Real) := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcomponent)
      (Nat.cast_nonneg _)
  have hdonorSubset : R.prechargeDonorSet ⊆ Finset.Ioc n (3 * n) := by
    intro a ha
    have haIoc := Finset.mem_Ioc.mp (R.prechargeDonorSet_subset_tail ha)
    exact Finset.mem_Ioc.mpr ⟨by omega, haIoc.2.trans hendpoint⟩
  have hbaseSubset : R.prechargeBaseState ⊆ Finset.Ioc n (3 * n) := by
    intro a ha
    have haIoc : n < a ∧ a ≤ M := by
      simpa only [factorInterval, Finset.mem_Ioc] using
        R.prechargeBaseState_subset_factorInterval ha
    exact Finset.mem_Ioc.mpr ⟨haIoc.1, haIoc.2.trans hendpoint⟩
  have haltSubset : R.prechargeAlternateState ⊆ Finset.Ioc n (3 * n) := by
    intro a ha
    have haIoc : n < a ∧ a ≤ M := by
      simpa only [factorInterval, Finset.mem_Ioc] using
        R.prechargeAlternateState_subset_factorInterval ha
    exact Finset.mem_Ioc.mpr ⟨haIoc.1, haIoc.2.trans hendpoint⟩
  constructor
  · calc
      (∑ a ∈ R.prechargeDonorSet, (a.factorization p : Real)) ≤
          (R.prechargeDonorSet.card : Real) *
            (Nat.log 2 (3 * n) : Real) :=
        sum_factorization_cast_le_card_mul_log_two hp hdonorSubset
      _ = (Fintype.card (BankPaperMarkerRequest n) : Real) *
            (Nat.log 2 (3 * n) : Real) := by
        rw [R.prechargeDonorSet_card]
      _ ≤ _ := hcardScale
  · constructor
    · calc
        (∑ a ∈ R.prechargeBaseState, (a.factorization p : Real)) ≤
            (R.prechargeBaseState.card : Real) *
              (Nat.log 2 (3 * n) : Real) :=
          sum_factorization_cast_le_card_mul_log_two hp hbaseSubset
        _ = (Fintype.card (BankPaperMarkerRequest n) : Real) *
              (Nat.log 2 (3 * n) : Real) := by
          rw [R.prechargeBaseState_card]
        _ ≤ _ := hcardScale
    · calc
        (∑ a ∈ R.prechargeAlternateState,
            (a.factorization p : Real)) ≤
            (R.prechargeAlternateState.card : Real) *
              (Nat.log 2 (3 * n) : Real) :=
          sum_factorization_cast_le_card_mul_log_two hp haltSubset
        _ = (Fintype.card (BankPaperMarkerRequest n) : Real) *
              (Nat.log 2 (3 * n) : Real) := by
          rw [R.prechargeAlternateState_card]
        _ ≤ _ := hcardScale





set_option maxHeartbeats 8000000 in
/-- Complete finite estimate for the literal three-term guard difference.
The raw-weight premise is only feasibility on the literal raw candidate
set; no signed cancellation and no exceptional-charge estimate is used. -/
theorem abs_roughCanonicalAggregateGuardResidual_le_majorant
    {c : Real} {depth n h W K p : Nat} {left right : Nat → Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (rawWeight : Nat → Real)
    (hweight : ∀ a ∈ roughRawCandidateSet n h K,
      0 ≤ rawWeight a ∧ rawWeight a ≤ 1)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWp : W < p) (hpY : p ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hp : p.Prime) (hendpoint : upperEndpoint n h ≤ 3 * n) :
    abs (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
      rawWeight p) ≤ roughCanonicalAggregateGuardResidualMajorant n := by
  let deleted := R.roughCanonicalNonexceptionalGuardDeletedSet certificate
    deltaStar K
  let donors := R.roughCanonicalExceptionalDonorSet deltaStar
  have hdeletedWeight : ∀ a ∈ deleted,
      0 ≤ rawWeight a ∧ rawWeight a ≤ 1 := by
    intro a ha
    exact hweight a
      ((R.mem_roughCanonicalNonexceptionalGuardDeletedSet certificate
        deltaStar).mp ha).1
  have hdeletedSupport : deleted ⊆
      certificate.anchors ∪ R.prechargeBaseState ∪
        R.prechargeAlternateState := by
    exact R.roughCanonicalNonexceptionalGuardDeletedSet_subset_support
      certificate deltaStar K
  have hdeleted :
      abs (∑ a ∈ deleted,
          rawWeight a * (a.factorization p : Real)) ≤
        (∑ a ∈ certificate.anchors, (a.factorization p : Real)) +
          (∑ a ∈ R.prechargeBaseState,
            (a.factorization p : Real)) +
          ∑ a ∈ R.prechargeAlternateState,
            (a.factorization p : Real) := by
    calc
      abs (∑ a ∈ deleted,
          rawWeight a * (a.factorization p : Real)) ≤
          ∑ a ∈ deleted, (a.factorization p : Real) :=
        abs_sum_weight_mul_factorization_le_sum_factorization hdeletedWeight
      _ ≤ ∑ a ∈
          certificate.anchors ∪ R.prechargeBaseState ∪
            R.prechargeAlternateState,
          (a.factorization p : Real) :=
        Finset.sum_le_sum_of_subset_of_nonneg hdeletedSupport
          (fun (a : Nat) _ha _hnew ↦
            Nat.cast_nonneg (a.factorization p))
      _ ≤ ((∑ a ∈ certificate.anchors,
            (a.factorization p : Real)) +
          ∑ a ∈ R.prechargeBaseState,
            (a.factorization p : Real)) +
          ∑ a ∈ R.prechargeAlternateState,
            (a.factorization p : Real) := by
        have houterUnion := sum_factorization_union_le
          (certificate.anchors ∪ R.prechargeBaseState)
          R.prechargeAlternateState p
        have hinnerUnion := sum_factorization_union_le certificate.anchors
          R.prechargeBaseState p
        exact houterUnion.trans (add_le_add hinnerUnion le_rfl)
  have hdonorsSubset : donors ⊆ R.prechargeDonorSet := by
    exact R.roughCanonicalExceptionalDonorSet_subset_prechargeDonorSet
      deltaStar
  have hdonors :
      abs (∑ a ∈ donors, (a.factorization p : Real)) ≤
        ∑ a ∈ R.prechargeDonorSet,
          (a.factorization p : Real) := by
    rw [abs_of_nonneg (by positivity :
      0 ≤ ∑ a ∈ donors, (a.factorization p : Real))]
    exact Finset.sum_le_sum_of_subset_of_nonneg hdonorsSubset
      (fun (a : Nat) _ha _hnew ↦ Nat.cast_nonneg (a.factorization p))
  have hbaseAbs :
      abs (∑ a ∈ R.prechargeBaseState,
        (a.factorization p : Real)) =
      ∑ a ∈ R.prechargeBaseState,
        (a.factorization p : Real) := by
    rw [abs_of_nonneg]
    positivity
  have hanchor :=
    sum_guardedCentralAnchors_factorization_le_two_mul_log_two
      certificate hTwoW hPrefix hWp hpY hyCutoff hp
  have hbank := R.precharge_guard_state_factorization_bounds hp hendpoint
  have hcomponents :=
    R.abs_roughCanonicalAggregateGuardResidual_le_components certificate
      deltaStar K rawWeight p
  change abs (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
      rawWeight p) ≤ roughCanonicalAggregateGuardResidualMajorant n
  change abs (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
      rawWeight p) ≤ _ at hcomponents
  change abs (∑ a ∈ deleted,
      rawWeight a * (a.factorization p : Real)) ≤ _ at hdeleted
  change abs (∑ a ∈ donors, (a.factorization p : Real)) ≤ _ at hdonors
  rw [hbaseAbs] at hcomponents
  calc
    abs (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
        rawWeight p) ≤
      ((∑ a ∈ certificate.anchors, (a.factorization p : Real)) +
          (∑ a ∈ R.prechargeBaseState, (a.factorization p : Real)) +
          ∑ a ∈ R.prechargeAlternateState, (a.factorization p : Real)) +
        (∑ a ∈ R.prechargeDonorSet, (a.factorization p : Real)) +
        ∑ a ∈ R.prechargeBaseState, (a.factorization p : Real) := by
      exact hcomponents.trans
        (add_le_add (add_le_add hdeleted hdonors) le_rfl)
    _ ≤
      ((2 * (Nat.log 2 (3 * n) : Real) +
          (bankPaperAnchorMarkerBudget n : Real) *
            (Nat.log 2 (3 * n) : Real)) +
          (bankPaperAnchorMarkerBudget n : Real) *
            (Nat.log 2 (3 * n) : Real)) +
        (bankPaperAnchorMarkerBudget n : Real) *
          (Nat.log 2 (3 * n) : Real) +
        (bankPaperAnchorMarkerBudget n : Real) *
          (Nat.log 2 (3 * n) : Real) := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (add_le_add hanchor hbank.2.1)
            hbank.2.2)
          hbank.1)
        hbank.2.1
    _ = roughCanonicalAggregateGuardResidualMajorant n := by
      unfold roughCanonicalAggregateGuardResidualMajorant
      ring

/-! ## Uniform absorption of the guard majorant -/















/-! ## Literal aggregate nonsmooth row correction -/





















/-! ## Exact final sign ledger and quantitative reduction -/





























end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {c : Real} {depth n h W K p : Nat} {left right : Nat → Nat} {changed : Finset.{0} Nat}
  (R : Erdos390.WholePaper.BankPaperRealization n (Erdos390.WholePaper.upperEndpoint n h))
  (certificate : Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n left right changed) (deltaStar : Real)
  (rawWeight : Nat → Real),
  (∀ (a : Nat),
      Membership.mem.{0, 0} (Erdos390.WholePaper.roughRawCandidateSet n h K) a →
        And (LE.le.{0} (0 : Real) (rawWeight a)) (LE.le.{0} (rawWeight a) (1 : Real))) →
    LE.le.{0} (2 : Nat) W →
      LE.le.{0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) depth) (1 : Nat)) W →
        LT.lt.{0} W p →
          LE.le.{0} p (Erdos390.Full.ArithmeticModel.yNat n) →
            LT.lt.{0} (Erdos390.Full.ArithmeticModel.yNat n) (Erdos390.WholePaper.centralAnchorCutoff depth n) →
              Nat.Prime p →
                LE.le.{0} (Erdos390.WholePaper.upperEndpoint n h) (HMul.hMul.{0, 0, 0} (3 : Nat) n) →
                  LE.le.{0}
                    (abs.{0}
                      (Erdos390.WholePaper.BankPaperRealization.roughCanonicalAggregateGuardResidual R certificate
                        deltaStar K rawWeight p))
                    (Erdos390.WholePaper.BankPaperRealization.roughCanonicalAggregateGuardResidualMajorant n) := by
  exact @Erdos390.WholePaper.BankPaperRealization.abs_roughCanonicalAggregateGuardResidual_le_majorant
