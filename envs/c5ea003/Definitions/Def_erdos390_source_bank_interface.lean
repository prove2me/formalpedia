-- Prove2me | Definitions.Def_erdos390_source_bank_interface
-- name    : erdos390_source_bank_interface
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T10:39:26.209292+00:00
-- url     : https://prove2.me/theorems/7696fa82-bc7b-4cf0-b3cb-d1991fb027f8
-- title:
--   Guarded central anchors, signed banks, and the common-depth construction interface
-- statement:
--   This file defines the finite arithmetic data used in the source construction for Erdős problem 390. For integers $n,M$, the factor interval is the set of integers in $(n,M]$. A guarded central-anchor certificate records central factors, an auxiliary divisor, the binomial-coefficient product identity, and exclusions needed to keep the remaining factors disjoint from the anchors. A signed prime-power bank records admissible local changes of factors and the prime-valuation corrections those changes produce.
--
--   The interface also defines complete rough-row labels, fractional and integral selection data, and the exact precharged tail target. Its two final predicates are fixed-depth capacity and post-tangent continuation. Capacity provides eventual compatible bank and anchor data with the required divisibility identities. Continuation converts such capacity data into eventual fractional selection data satisfying the exact row, valuation, interval, and disjointness constraints. These are predicates, not assertions that the required data exist. The file includes the proved structural and constructor lemmas needed to define the data; the common-depth existence assertion is a separate theorem.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalFixedDepthCapacityBridge.lean#L30-L52 ; https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalUpperConstructionEventually.lean#L30-L140 ; foundational declarations are extracted without changing their bodies from the source modules identified in the file comments.

import Mathlib

namespace Erdos390.Full.Scale
end Erdos390.Full.Scale


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

/-- The real smoothness threshold from the paper, `n^(2/9)`. -/
noncomputable def y (n : ℕ) : ℝ :=
  (n : ℝ) ^ (2 / 9 : ℝ)

/-- The integral cutoff used when a finite set of primes is required. -/
noncomputable def yNat (n : ℕ) : ℕ :=
  ⌊y n⌋₊



































































































end Erdos390.Full.ArithmeticModel

end

/- Source module: Erdos390.WholePaper.BankMarkerDonorCombinatorics -/
section


/-!
# Finite marker--donor combinatorics

This file treats eligibility as an actual finite relation of marker--donor
pairs.  It proves only finite double counting, bounded-multiplicity counting,
choice of one donor already present in the relation, and a balanced split of
the chosen pairs into two orientation pools.  It makes no prime-number-theorem
or asymptotic supply assertion.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



/-- The actual markers occurring in at least one eligible pair. -/
def bankEligibleMarkers {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) : Finset Marker :=
  eligible.image Prod.fst











 theorem eligibleMarker_exists_donor
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor))
    {marker : Marker} (hmarker : marker ∈ bankEligibleMarkers eligible) :
    ∃ donor, (marker, donor) ∈ eligible := by
  rcases Finset.mem_image.mp hmarker with ⟨⟨marker', donor⟩, hpair, hmarker'⟩
  subst marker
  exact ⟨donor, hpair⟩

/-- An actual eligible donor chosen for a marker in the finite support. -/
def bankChosenDonor
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor))
    (marker : ↑(bankEligibleMarkers eligible)) : Donor :=
  Classical.choose (eligibleMarker_exists_donor eligible marker.property)

/-- The chosen marker together with its chosen actual donor. -/
def bankChosenMarkerDonor
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor))
    (marker : ↑(bankEligibleMarkers eligible)) : Marker × Donor :=
  (marker.1, bankChosenDonor eligible marker)





/-- The finite set consisting of one actual donor pair for every eligible marker. -/
def bankMarkerDonorPairs
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) : Finset (Marker × Donor) :=
  (bankEligibleMarkers eligible).attach.image
    (bankChosenMarkerDonor eligible)









 theorem half_card_subset_exists {Pair : Type*} [DecidableEq Pair]
    (pairs : Finset Pair) :
    ∃ pool ⊆ pairs, pool.card = pairs.card / 2 := by
  exact Finset.exists_subset_card_eq (Nat.div_le_self pairs.card 2)

/-- One orientation pool, chosen to contain exactly half the selected pairs,
rounded down. -/
def bankOrientationPoolFirst
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) : Finset (Marker × Donor) :=
  Classical.choose (half_card_subset_exists (bankMarkerDonorPairs eligible))

/-- The complementary orientation pool. -/
def bankOrientationPoolSecond
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) : Finset (Marker × Donor) :=
  bankMarkerDonorPairs eligible \ bankOrientationPoolFirst eligible



















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomPoolMatching -/
section


/-!
# Finite matching for the eight oriented bottom pools

The four bottom moves and their two orientations give eight literal pool
labels.  This file assumes only actual finite request and occurrence pools,
pointwise cardinality bounds, and pairwise disjointness of the occurrence
pools.  It then chooses an injective occurrence assignment.  No analytic
estimate asserting that the capacity hypotheses hold appears here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The four bottom moves in the bank descent. -/
inductive BankBottomMove where
  | fiveToFour
  | fourToThree
  | threeToTwo
  | twoToOne
  deriving DecidableEq, Fintype

/-- The two copies used for opposite path orientations. -/
inductive BankBottomOrientation where
  | downward
  | upward
  deriving DecidableEq, Fintype

/-- One of the eight bottom move/orientation pools. -/
abbrev BankBottomOrientationPool := BankBottomMove × BankBottomOrientation









































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.Definitions -/
section


/-!
# Exact definitions for Erdős Problem 390

This file fixes the literal finite combinatorial object and the exact
asymptotic target used by the paper.  A `Finset` represents the distinct
factors: after sorting it, its elements are precisely a strictly increasing
list `a₁ < ... < aₖ`.

The quotient `M! / (n!)²` is deliberately valued in `ℚ`.  It must not be
defined with `Nat.div`: before admissibility has been proved, `(n!)²` need
not divide `M!`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The literal integer interval `(n, M]` from the paper. -/
def factorInterval (n M : ℕ) : Finset ℕ :=
  Finset.Ioc n M







/-- The exact rational constant in the paper. -/
def C0 : ℝ :=
  (4029639598 : ℝ) / 25970038185

/-- The natural second-order scale `n / log n`. -/
def secondOrderScale (n : ℕ) : ℝ :=
  (n : ℝ) / Real.log (n : ℝ)















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

/-- The paper's integral upper-tail length at fixed positive scale `c`. -/
def upperTailLength (c : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (c * secondOrderScale n)

/-- The endpoint obtained by adjoining a tail of length `h` above `2n`. -/
def upperEndpoint (n h : ℕ) : ℕ :=
  2 * n + h







































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

/-- Open lower endpoint of a bottom marker interval. -/
def bankBottomMarkerLower (n : ℕ) : BankBottomMove → ℕ
  | .fiveToFour => n / 3
  | .fourToThree => 2 * n / 5
  | .threeToTwo => 2 * n / 3
  | .twoToOne => n / 2

/-- Closed upper endpoint of a bottom marker interval. -/
def bankBottomMarkerUpper (M : ℕ) : BankBottomMove → ℕ
  | .fiveToFour => M / 6
  | .fourToThree => M / 5
  | .threeToTwo => M / 3
  | .twoToOne => M / 4

/-- The four literal marker intervals from the bottom-pool table. -/
def bankBottomMarkerInterval (n M : ℕ)
    (move : BankBottomMove) : Finset ℕ :=
  Finset.Ioc (bankBottomMarkerLower n move)
    (bankBottomMarkerUpper M move)

/-- Integer midpoint used for the fixed one-half orientation split. -/
def bankBottomOrientationCut (n M : ℕ)
    (move : BankBottomMove) : ℕ :=
  bankBottomMarkerLower n move +
    (bankBottomMarkerUpper M move - bankBottomMarkerLower n move) / 2

/-- The two adjacent orientation subintervals of one bottom marker pool. -/
def bankBottomOrientedMarkerInterval (n M : ℕ)
    (pool : BankBottomOrientationPool) : Finset ℕ :=
  match pool.2 with
  | .downward => Finset.Ioc (bankBottomMarkerLower n pool.1)
      (bankBottomOrientationCut n M pool.1)
  | .upward => Finset.Ioc (bankBottomOrientationCut n M pool.1)
      (bankBottomMarkerUpper M pool.1)

/-- Prime markers in one oriented bottom pool. -/
def bankBottomOrientedMarkerPrimes (n M : ℕ)
    (pool : BankBottomOrientationPool) : Finset ℕ :=
  (bankBottomOrientedMarkerInterval n M pool).filter Nat.Prime



/-- Multiplier of the smaller endpoint state in each row. -/
def bankBottomLowerStateMultiplier : BankBottomMove → ℕ
  | .fiveToFour => 4
  | .fourToThree => 3
  | .threeToTwo => 2
  | .twoToOne => 2

/-- Multiplier of the larger endpoint state in each row. -/
def bankBottomUpperStateMultiplier : BankBottomMove → ℕ
  | .fiveToFour => 5
  | .fourToThree => 4
  | .threeToTwo => 3
  | .twoToOne => 4

/-- Multiplier of the backing donor occurrence in each row. -/
def bankBottomDonorMultiplier : BankBottomMove → ℕ
  | .fiveToFour => 6
  | .fourToThree => 5
  | .threeToTwo => 3
  | .twoToOne => 4

def bankBottomLowerState (move : BankBottomMove) (marker : ℕ) : ℕ :=
  bankBottomLowerStateMultiplier move * marker

def bankBottomUpperState (move : BankBottomMove) (marker : ℕ) : ℕ :=
  bankBottomUpperStateMultiplier move * marker

def bankBottomDonor (move : BankBottomMove) (marker : ℕ) : ℕ :=
  bankBottomDonorMultiplier move * marker

/-- The actual occurrences named by one bottom component.  A donor equal to
a state is represented once because this is a `Finset`. -/
def bankBottomComponentOccurrences
    (move : BankBottomMove) (marker : ℕ) : Finset ℕ :=
  {bankBottomLowerState move marker,
    bankBottomUpperState move marker,
    bankBottomDonor move marker}



































end

end Erdos390.WholePaper

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

/-- A finite list of distinct head primes and their prescribed exponents. -/
structure Pattern where
  primes : Finset ℕ
  exponent : ℕ → ℕ
  prime_mem : ∀ p ∈ primes, p.Prime

namespace Pattern

variable (P : Pattern)





/-- Exact agreement with the prescribed head valuations. -/
def Matches (m : ℕ) : Prop :=
  ∀ p ∈ P.primes, m.factorization p = P.exponent p

instance (m : ℕ) : Decidable (P.Matches m) := by
  unfold Matches
  infer_instance



























end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.WholePaper.BankPathAlgebra -/
section


/-!
# Exact finite algebra of the universal bank paths

This module isolates the algebraic part of the paper's precharged bank.  It
contains no prime-supply, donor, congestion, or asymptotic hypothesis:
ordinary component changes telescope, the four displayed bottom changes
complete a prime-to-five descent to a signed unit vector, reversing a path
reverses that sign, and finitely many copies of both orientations realize
every integral vector in the prescribed box.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Integer-valued prime-coordinate vectors. -/
abbrev BankVector (I : Type*) := I → ℤ

/-- The coordinate unit vector at `p`. -/
def coordinateUnit {I : Type*} [DecidableEq I] (p : I) : BankVector I :=
  fun q ↦ if p = q then 1 else 0

/-- The complete integer valuation vector of a natural number. -/
def integerValuationVector (a : ℕ) : BankVector ℕ :=
  fun p ↦ (a.factorization p : ℤ)







/-- Signed valuation change of a component whose source core is replaced by
its target core. -/
def factorMoveChange (source target : ℕ) : BankVector ℕ :=
  integerValuationVector target - integerValuationVector source







/-- The four literal bottom changes from the paper. -/
def bottomFiveToFourChange : BankVector ℕ :=
  (2 : ℤ) • coordinateUnit 2 - coordinateUnit 5

def bottomFourToThreeChange : BankVector ℕ :=
  coordinateUnit 3 - (2 : ℤ) • coordinateUnit 2

def bottomThreeToTwoChange : BankVector ℕ :=
  coordinateUnit 2 - coordinateUnit 3

def bottomTwoToOneChange : BankVector ℕ :=
  -coordinateUnit 2









/-- Total change of the four bottom moves `5→4→3→2→1`. -/
def fourBottomMovesChange : BankVector ℕ :=
  bottomFiveToFourChange + bottomFourToThreeChange +
    bottomThreeToTwoChange + bottomTwoToOneChange













/-- Net vector change obtained by using `positive p` positive-unit paths and
`negative p` negative-unit paths at every coordinate. -/
def signedUnitPathChange {I : Type*} [Fintype I] [DecidableEq I]
    (positive negative : I → ℕ) : BankVector I :=
  ∑ p : I, (
    (positive p : ℤ) • coordinateUnit p +
      (negative p : ℤ) • (-coordinateUnit p))



/-- Positive and negative counts canonically associated with an integral
target coordinate. -/
def positiveUnitPathCount {I : Type*} (z : BankVector I) (p : I) : ℕ :=
  (z p).toNat

def negativeUnitPathCount {I : Type*} (z : BankVector I) (p : I) : ℕ :=
  (-z p).toNat



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.GuardedBankSelection -/
section


/-! # Explicit finite selection from a two-sided signed-unit bank -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

abbrev SignedBankSlot {P : Type*} (β : P → ℕ) :=
  Σ p : P, Sum (Fin (β p)) (Fin (β p))



/-- Embed a finite coordinate vector into an actual target coordinate type. -/
def embeddedBankVector {P Q : Type*} [Fintype P] [DecidableEq Q]
    (coordinate : P → Q) (z : BankVector P) : BankVector Q :=
  ∑ p : P, (z p) • coordinateUnit (coordinate p)

/-- Actual-coordinate unit change of one signed bank slot. -/
def embeddedSignedBankSlotChange
    {P Q : Type*} [DecidableEq Q] {β : P → ℕ}
    (coordinate : P → Q) (g : SignedBankSlot β) : BankVector Q :=
  match g.2 with
  | Sum.inl _ => coordinateUnit (coordinate g.1)
  | Sum.inr _ => -coordinateUnit (coordinate g.1)

def signedBankStateChoice {P : Type*} {β : P → ℕ}
    (positive negative : P → ℕ) (g : SignedBankSlot β) : Bool :=
  match g.2 with
  | Sum.inl i => decide (i.1 < positive g.1)
  | Sum.inr i => decide (i.1 < negative g.1)













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomConcreteDemand -/
section


/-!
# Concrete request demand for the eight bottom bank pools

The formal floating-rounding theorem produces the sharper floor-log error box
`4 * log_2(M) * log_p(M)`.  We reserve the paper's ceiling-log,
endpoint-free box at `3n`.  A request is an actual signed bank
slot together with one of the four bottom moves; its sign selects the fixed
orientation pool.  Thus every one of the eight pool fibers has exactly
`sum_{p <= floor(n^(2/9))} beta_p` requests.

The analytic count is also proved here.  Primes below `(3n)^(1/5)` are
bounded trivially; their contribution is `o(n^(2/9))`.  Above that cutoff,
`clog_p(3n) <= 5`, while the safe PNT gives `pi(y) = O(y / log y)`.  Since
`log y` is a fixed positive fraction of `log n`, the total demand is
`O(y)`, hence negligible compared with `n / (log n)^2`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-- The actual finite prime support of the rounding error box. -/
def bankRoundingPrimeSupport (n : ℕ) : Finset ℕ :=
  (yNat n + 1).primesBelow

/-- Common binary logarithmic degree, with the eventual endpoint already
majorized by `3n`. -/
def bankRoundingDepth (n : ℕ) : ℕ :=
  Nat.clog 2 (3 * n)

/-- Number of copies of each sign reserved at a supported prime.  Both
logarithmic factors are literal natural ceilings, as in the paper. -/
def bankRoundingBeta (n p : ℕ) : ℕ :=
  4 * bankRoundingDepth n * Nat.clog p (3 * n)





/-- The same copy count on the subtype used by `SignedBankSlot`. -/
def bankRoundingBetaOnSupport (n : ℕ) : ↑(bankRoundingPrimeSupport n) → ℕ :=
  fun p ↦ bankRoundingBeta n p.1







/-- One concrete request is a signed prime-copy slot together with one of
the four bottom moves traversed by that signed path. -/
abbrev BankBottomPaperRequest (n : ℕ) :=
  SignedBankSlot (bankRoundingBetaOnSupport n) × BankBottomMove

/-- The sign of a reserved slot chooses one of the two midpoint halves. -/
def bankSignedSlotOrientation
    {P : Type*} {β : P → ℕ} (slot : SignedBankSlot β) :
    BankBottomOrientation :=
  match slot.2 with
  | .inl _copy => .downward
  | .inr _copy => .upward

/-- Literal routing of a path request to one of the eight pools. -/
def bankBottomPaperRequestPool (n : ℕ) :
    BankBottomPaperRequest n → BankBottomOrientationPool :=
  fun request ↦ (request.2, bankSignedSlotOrientation request.1)

/-- The actual finite family containing every signed-copy/move request. -/
def bankBottomPaperRequests (n : ℕ) : Finset (BankBottomPaperRequest n) :=
  Finset.univ













































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankRoughSignatures -/
section


/-!
# Complete rough signatures and bank path row counts

The complete rough signature keeps every prime-power exponent above a fixed
cutoff.  Its integer label is the corresponding product of prime powers.
Unique factorization proves that the vector and integer labels induce exactly
the same partition.  Separately, componentwise equality of signatures is
used to derive full path-state multiplicity invariance; it is not stored as a
field or assumed for the completed path.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- The vector convention `S(a)=(v_P(a))_{P>y}` for a complete rough
signature. -/
def completeRoughSignature (y a : ℕ) : ℕ →₀ ℕ :=
  a.factorization.filter (fun p ↦ y < p)



/-- The integer convention `R_y(a)`, retaining the same prime-power
multiplicities as the vector convention. -/
def completeRoughLabel (y a : ℕ) : ℕ :=
  (completeRoughSignature y a).prod (fun p e ↦ p ^ e)







/-- Number of factors in a finite state having one specified complete
signature. -/
def completeSignatureMultiplicity
    (y : ℕ) (state : Finset ℕ) (signature : ℕ →₀ ℕ) : ℕ :=
  (state.filter (fun a ↦ completeRoughSignature y a = signature)).card





/-- A full path state contains one token for each component index. -/
def indexedPathState {C : Type*} [Fintype C] [DecidableEq C]
    (state : C → ℕ) : Finset ℕ :=
  Finset.univ.image state





/-- Signature multiplicity before forgetting component indices. -/
def componentSignatureMultiplicity
    {C : Type*} [Fintype C] [DecidableEq C]
    (y : ℕ) (state : C → ℕ) (signature : ℕ →₀ ℕ) : ℕ :=
  (Finset.univ.filter
    (fun c ↦ completeRoughSignature y (state c) = signature)).card







end

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

/-- The stationary prime layer in row `r`, with open lower endpoint and
closed upper endpoint.  Both endpoint conditions are recorded as exact
integer inequalities. -/
def stationaryPrimeLayer (n r : ℕ) : Finset ℕ :=
  (Finset.range (2 * n + 1)).filter fun p ↦
    p.Prime ∧ n < p * (r + 1) ∧ p * (2 * r + 1) ≤ 2 * n



















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

/-- Source prime carried by a concrete bottom request. -/
def bankBottomPaperRequestPrime {n : ℕ}
    (request : BankBottomPaperRequest n) : ℕ :=
  request.1.1.1



/-- The two small state cores in each displayed bottom row. -/
def bankBottomIncidentStateCores (move : BankBottomMove) : ℕ × ℕ :=
  (bankBottomLowerStateMultiplier move,
    bankBottomUpperStateMultiplier move)









/-- Relevance of one displayed row to a source prime. -/
def bankBottomMoveRelevantForPrime (prime : ℕ) : BankBottomMove → Prop
  | .fiveToFour => 5 ≤ prime
  | .fourToThree => 5 ≤ prime
  | .threeToTwo => 3 ≤ prime
  | .twoToOne => 2 ≤ prime

instance bankBottomMoveRelevantForPrime_decidable (prime : ℕ)
    (move : BankBottomMove) :
    Decidable (bankBottomMoveRelevantForPrime prime move) := by
  cases move <;> unfold bankBottomMoveRelevantForPrime <;> infer_instance

/-- The literal finite row set in the truncated bottom path. -/
def bankBottomRelevantMoves (prime : ℕ) : Finset BankBottomMove :=
  Finset.univ.filter (bankBottomMoveRelevantForPrime prime)









/-- A row is used precisely when it lies on the source prime's truncated
bottom path.  Thus primes at least five use all four rows, prime three uses
the last two, and prime two uses only the last row. -/
def bankBottomPaperRequestRelevant {n : ℕ}
    (request : BankBottomPaperRequest n) : Prop :=
  bankBottomMoveRelevantForPrime (bankBottomPaperRequestPrime request)
    request.2

instance bankBottomPaperRequestRelevant_decidable {n : ℕ}
    (request : BankBottomPaperRequest n) :
    Decidable (bankBottomPaperRequestRelevant request) := by
  unfold bankBottomPaperRequestRelevant
  infer_instance

theorem bankBottomPaperRequestRelevant_iff_mem_moves
    {n : ℕ} (request : BankBottomPaperRequest n) :
    bankBottomPaperRequestRelevant request ↔
      request.2 ∈ bankBottomRelevantMoves
        (bankBottomPaperRequestPrime request) := by
  simp [bankBottomPaperRequestRelevant, bankBottomRelevantMoves]

/-- The requests that really occur in their source prime's bottom path. -/
def bankBottomRelevantPaperRequests (n : ℕ) :
    Finset (BankBottomPaperRequest n) :=
  (bankBottomPaperRequests n).filter bankBottomPaperRequestRelevant













/-- Forget relevance while retaining membership in the full matched family. -/
def bankBottomRelevantRequestToPaperRequest {n : ℕ}
    (request : ↑(bankBottomRelevantPaperRequests n)) :
    ↑(bankBottomPaperRequests n) :=
  ⟨request.1, (Finset.mem_filter.mp request.property).1⟩

theorem bankBottomRelevantRequestToPaperRequest_injective {n : ℕ} :
    Function.Injective
      (bankBottomRelevantRequestToPaperRequest (n := n)) := by
  intro request request' heq
  apply Subtype.ext
  exact congrArg (fun x : ↑(bankBottomPaperRequests n) ↦ x.1) heq

/-! ## The deterministic truncated bottom path -/

/-- Valuation change of one downward bottom row.  The last row is represented
by its actual state factors `4P -> 2P`; after cancelling the common marker its
change is the paper's `2 -> 1` vector `-e_2`. -/
def bankBottomMoveChange (move : BankBottomMove) : BankVector ℕ :=
  factorMoveChange (bankBottomUpperStateMultiplier move)
    (bankBottomLowerStateMultiplier move)











/-- The unsigned downward change obtained by traversing exactly the bottom
rows relevant to `prime`.  Padding requests from the rectangular matching do
not occur in this sum. -/
def bankBottomPathChange (prime : ℕ) : BankVector ℕ :=
  ∑ move ∈ bankBottomRelevantMoves prime, bankBottomMoveChange move







/-- The full-family matched request attached to a slot and a row.  A separate
membership theorem below records when this request belongs to the literal
truncated path. -/
def bankBottomPaperRequestOfMove {n : ℕ}
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (move : BankBottomMove) : ↑(bankBottomPaperRequests n) :=
  ⟨(slot, move), Finset.mem_univ _⟩



/-! ## A realization obtained from the actual matching -/

/-- An actual marker realization for the complete rectangular request family.
Only `bankBottomRelevantPaperRequests` is used when forming the final bank. -/
structure BankBottomPaperRealization (n M : ℕ) where
  marker : ↑(bankBottomPaperRequests n) → ℕ
  marker_mem : ∀ request,
    marker request ∈ bankBottomOrientedMarkerPrimes n M
      (bankBottomPaperRequestPool n request.1)
  marker_injective : Function.Injective marker



namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)

def move (_realization : BankBottomPaperRealization n M)
    (request : ↑(bankBottomPaperRequests n)) : BankBottomMove :=
  request.1.2

def lowerStateFactor (request : ↑(bankBottomPaperRequests n)) : ℕ :=
  bankBottomLowerState (realization.move request) (realization.marker request)

def upperStateFactor (request : ↑(bankBottomPaperRequests n)) : ℕ :=
  bankBottomUpperState (realization.move request) (realization.marker request)

def donorFactor (request : ↑(bankBottomPaperRequests n)) : ℕ :=
  bankBottomDonor (realization.move request) (realization.marker request)

/-- The pair of incident state cores before multiplication by the marker. -/
def incidentStateCores (request : ↑(bankBottomPaperRequests n)) : ℕ × ℕ :=
  bankBottomIncidentStateCores (realization.move request)



















/-! The four paper rows, with the marker made explicit. -/













/-! ## Orientation-aware realized row and slot changes -/

/-- The state occupied before traversing a realized bottom row.  Downward
slots start at the larger state; upward slots start at the smaller state. -/
def fromStateValue (request : ↑(bankBottomPaperRequests n)) : ℕ :=
  match bankSignedSlotOrientation request.1.1 with
  | .downward => realization.upperStateFactor request
  | .upward => realization.lowerStateFactor request

/-- The state occupied after traversing a realized bottom row. -/
def toStateValue (request : ↑(bankBottomPaperRequests n)) : ℕ :=
  match bankSignedSlotOrientation request.1.1 with
  | .downward => realization.lowerStateFactor request
  | .upward => realization.upperStateFactor request

/-- Actual valuation change of one realized bottom component. -/
def realizedComponentChange
    (request : ↑(bankBottomPaperRequests n)) : BankVector ℕ :=
  factorMoveChange (realization.fromStateValue request)
    (realization.toStateValue request)





/-- Total actual bottom change of a signed slot.  The sum is deliberately
indexed by `bankBottomRelevantMoves`, so unused rectangular-family matches
cannot enter the realized path. -/
def realizedSlotChange
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) : BankVector ℕ :=
  ∑ move ∈ bankBottomRelevantMoves slot.1.1,
    realization.realizedComponentChange
      (bankBottomPaperRequestOfMove slot move)

/-- Deterministic signed version of the truncated bottom path. -/
def signedBottomPathChange
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) : BankVector ℕ :=
  match slot.2 with
  | .inl _copy => bankBottomPathChange slot.1.1
  | .inr _copy => -bankBottomPathChange slot.1.1









end BankBottomPaperRealization

/-! ## Complete occurrence sets and rough signatures -/

/-- The four named roles.  Their images form a `Finset`, so equal roles such
as terminal-row donor/upper-state are represented by one occurrence. -/
inductive BankBottomPaperOccurrenceKind where
  | marker
  | lowerState
  | upperState
  | donor
  deriving DecidableEq, Fintype

def bankBottomPaperOccurrenceMultiplier
    (move : BankBottomMove) : BankBottomPaperOccurrenceKind → ℕ
  | .marker => 1
  | .lowerState => bankBottomLowerStateMultiplier move
  | .upperState => bankBottomUpperStateMultiplier move
  | .donor => bankBottomDonorMultiplier move





namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)

/-- Numerical value of one named occurrence in a realized component. -/
def occurrenceValue (request : ↑(bankBottomPaperRequests n))
    (kind : BankBottomPaperOccurrenceKind) : ℕ :=
  bankBottomPaperOccurrenceMultiplier (realization.move request) kind *
    realization.marker request









/-- Diagnostic carrier set used for marker recovery and cross-family collision
checks.  This is deliberately not the bank-factor census: the bare marker is
usually below `n` and is not a factor occurrence. -/
def carrierValueSet (request : ↑(bankBottomPaperRequests n)) : Finset ℕ :=
  (Finset.univ : Finset BankBottomPaperOccurrenceKind).image
    (realization.occurrenceValue request)









/-- The actual factor occurrences of a component.  In particular, this does
not contain the bare marker.  The `Finset` identifies the terminal-row donor
with the equal upper-state occurrence. -/
def componentOccurrences
    (request : ↑(bankBottomPaperRequests n)) : Finset ℕ :=
  bankBottomComponentOccurrences (realization.move request)
    (realization.marker request)

































end BankBottomPaperRealization

/-! ## Explicit local geometry and collision freedom -/



namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)









/-! ## Relevant markers and marker-to-component uniqueness -/

/-- Only markers of path-relevant requests are exposed to downstream anchor
guards.  Markers assigned to rectangular-family padding requests are absent. -/
def relevantMarkers : Finset ℕ :=
  (bankBottomRelevantPaperRequests n).attach.image
    (fun request ↦ realization.marker
      (bankBottomRelevantRequestToPaperRequest request))

/-- Actual bottom-bank factor census.  It unions only path-relevant
components, and each component contributes only its two states and donor;
bare marker primes and rectangular-family padding requests are excluded. -/
def relevantComponentOccurrences : Finset ℕ :=
  (bankBottomRelevantPaperRequests n).attach.biUnion
    (fun request ↦ realization.componentOccurrences
      (bankBottomRelevantRequestToPaperRequest request))

theorem relevantMarkerMap_injective : Function.Injective
    (fun request : ↑(bankBottomRelevantPaperRequests n) ↦
      realization.marker (bankBottomRelevantRequestToPaperRequest request)) :=
  realization.marker_injective.comp
    bankBottomRelevantRequestToPaperRequest_injective



theorem relevantMarker_existsUnique_request
    {marker : ℕ} (hmarker : marker ∈ realization.relevantMarkers) :
    ∃! request : ↑(bankBottomRelevantPaperRequests n),
      realization.marker (bankBottomRelevantRequestToPaperRequest request) =
        marker := by
  rw [relevantMarkers] at hmarker
  rcases Finset.mem_image.mp hmarker with
    ⟨request, _hrequest, hrequestMarker⟩
  refine ⟨request, hrequestMarker, ?_⟩
  intro request' hrequest'Marker
  exact realization.relevantMarkerMap_injective
    (hrequest'Marker.trans hrequestMarker.symm)

/-- The unique relevant request carried by a marker in the realized marker
set. -/
def requestForRelevantMarker (marker : ↑realization.relevantMarkers) :
    ↑(bankBottomRelevantPaperRequests n) :=
  Classical.choose
    (realization.relevantMarker_existsUnique_request marker.property)





/-- The two incident cores as a function of an actual relevant marker. -/
def relevantMarkerIncidentStateCores
    (marker : ↑realization.relevantMarkers) : ℕ × ℕ :=
  realization.incidentStateCores
    (bankBottomRelevantRequestToPaperRequest
      (realization.requestForRelevantMarker marker))









end BankBottomPaperRealization

/-! ## Cardinality bound for the actual relevant marker set -/







/-! ## Eventual local geometry and the terminal realized family -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankGeometricDescentCore -/
section


/-!
# Literal finite algebra for the large-core bank descent

This module contains only the discrete ceiling, power-of-two avoidance, and
exact inequalities used by the geometric descent in Section 5.  It has no
donor-counting or prime-distribution input.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- A computational characterization of the nonzero powers of two.  Using
`Nat.log` makes the finite small-table certificate kernel reducible. -/
def IsPowerOfTwo (m : ℕ) : Prop :=
  m = 2 ^ Nat.log 2 m

instance decidableIsPowerOfTwo (m : ℕ) : Decidable (IsPowerOfTwo m) := by
  unfold IsPowerOfTwo
  exact inferInstance





/-- The literal integer ceiling `b₀ = ⌈4q/5⌉`. -/
def largeCoreCeil (q : ℕ) : ℕ :=
  (4 * q) ⌈/⌉ 5



/-- The literal large-core rule: subtract one precisely when the ceiling is
a power of two. -/
def largeCoreStep (q : ℕ) : ℕ :=
  if IsPowerOfTwo (largeCoreCeil q) then largeCoreCeil q - 1
  else largeCoreCeil q











theorem largeCoreStep_le_ceil (q : ℕ) :
    largeCoreStep q ≤ largeCoreCeil q := by
  unfold largeCoreStep
  split <;> omega



/-- Exact upper cross-multiplication for
`largeCoreStep q < 4q/5 + 1`. -/
theorem largeCoreStep_cross_upper (q : ℕ) :
    5 * largeCoreStep q < 4 * q + 5 := by
  have hceil : 5 * largeCoreCeil q < 4 * q + 5 := by
    simp [largeCoreCeil, Nat.ceilDiv_eq_add_pred_div]
    omega
  have hle := largeCoreStep_le_ceil q
  omega

/-- In particular the core strictly decreases once `q ≥ 6`. -/
theorem largeCoreStep_lt_self {q : ℕ} (hq : 6 ≤ q) :
    largeCoreStep q < q := by
  have h := largeCoreStep_cross_upper q
  omega







/-- A source core lies in the paper's geometric cell `(Q,4Q/3]`. -/
def CoreInGeometricCell (Q : ℚ) (q : ℕ) : Prop :=
  Q < (q : ℚ) ∧ (q : ℚ) ≤ 4 * Q / 3

/-- The source and target satisfy all three strict/non-strict cell
inequalities used by an ordinary descent edge. -/
def InGeometricDescentCell (Q : ℚ) (q b : ℕ) : Prop :=
  CoreInGeometricCell Q q ∧ 3 * Q / 4 < (b : ℚ)







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankSmallDescentTable -/
section


/-!
# Kernel-checked finite table for the five small descent scales

The fifteen source/target pairs are the literal table in Section 5.  All
checks here are finite: strict descent, avoidance of powers of two, and the
three rational cell inequalities.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- The five nonbottom geometric scales at or below `20`. -/
inductive SmallDescentScale where
  | one
  | two
  | three
  | four
  | five
  deriving DecidableEq, Fintype

/-- Numerator of the exact rational value `Q_j = 4(4/3)^j`. -/
def smallDescentScaleNumerator : SmallDescentScale → ℕ
  | .one => 16
  | .two => 64
  | .three => 256
  | .four => 1024
  | .five => 4096

/-- Denominator of the exact rational value `Q_j = 4(4/3)^j`. -/
def smallDescentScaleDenominator : SmallDescentScale → ℕ
  | .one => 3
  | .two => 9
  | .three => 27
  | .four => 81
  | .five => 243

/-- The exact rational values `Q_j = 4(4/3)^j`, for `1 ≤ j ≤ 5`. -/
def smallDescentScaleValue (scale : SmallDescentScale) : ℚ :=
  smallDescentScaleNumerator scale / smallDescentScaleDenominator scale

/-- Literal source and target cell inequalities for one small scale. -/
def InSmallGeometricDescentCell
    (scale : SmallDescentScale) (q b : ℕ) : Prop :=
  smallDescentScaleValue scale < (q : ℚ) ∧
    (q : ℚ) ≤ 4 * smallDescentScaleValue scale / 3 ∧
    3 * smallDescentScaleValue scale / 4 < (b : ℚ)

/-- Exact natural-number cross-multiplications equivalent to the three cell
inequalities.  This is the form checked by kernel reduction. -/
def InSmallGeometricDescentCellCross
    (scale : SmallDescentScale) (q b : ℕ) : Prop :=
  smallDescentScaleNumerator scale <
      q * smallDescentScaleDenominator scale ∧
    3 * q * smallDescentScaleDenominator scale ≤
      4 * smallDescentScaleNumerator scale ∧
    3 * smallDescentScaleNumerator scale <
      4 * b * smallDescentScaleDenominator scale

instance decidableInSmallGeometricDescentCellCross
    (scale : SmallDescentScale) (q b : ℕ) :
    Decidable (InSmallGeometricDescentCellCross scale q b) := by
  unfold InSmallGeometricDescentCellCross
  exact inferInstance





/-- Reusable certificate carried by every displayed small-table pair. -/
def IsCertifiedSmallDescentPair (q b : ℕ) : Prop :=
  6 ≤ q ∧
    ¬ IsPowerOfTwo q ∧
    ¬ IsPowerOfTwo b ∧
    5 ≤ b ∧
    b < q ∧
    ∃ scale : SmallDescentScale,
      InSmallGeometricDescentCellCross scale q b

instance decidableIsCertifiedSmallDescentPair (q b : ℕ) :
    Decidable (IsCertifiedSmallDescentPair q b) := by
  unfold IsCertifiedSmallDescentPair
  exact inferInstance

/-- A certificate with its witnessing small scale made explicit. -/
def IsCertifiedSmallDescentEntry
    (scale : SmallDescentScale) (q b : ℕ) : Prop :=
  6 ≤ q ∧
    ¬ IsPowerOfTwo q ∧
    ¬ IsPowerOfTwo b ∧
    5 ≤ b ∧
    b < q ∧
    InSmallGeometricDescentCellCross scale q b

instance decidableIsCertifiedSmallDescentEntry
    (scale : SmallDescentScale) (q b : ℕ) :
    Decidable (IsCertifiedSmallDescentEntry scale q b) := by
  unfold IsCertifiedSmallDescentEntry
  exact inferInstance



/-- The unique small scale used by every source appearing in the table. -/
def smallDescentScaleForSource (q : ℕ) : SmallDescentScale :=
  if q ≤ 7 then .one
  else if q ≤ 9 then .two
  else if q ≤ 12 then .three
  else if q ≤ 15 then .four
  else .five











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryDonorRelation -/
section


/-!
# The ordinary-bank marker--donor relation

This file defines the literal finite relation used by the nonbottom bank in
Section 5.3.  The scale is rational, so the grid `Q_j = 4(4/3)^j` and all four
interval endpoints are represented without rounding.  The wider relation is
the actual relation from which marker--donor pairs are selected.  The narrow
relation is the bulk subrelation used in the analytic supply proof.

There is no prime-distribution input here.  In particular, the fiber bound is
an exact injection into the natural quotient interval
`(2n / P, M / P]`.  The five fixed small-scale donors are also recorded here,
including their literal rational interval checks.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- The exact rational geometric grid `Q_j = 4(4/3)^j`. -/
def bankOrdinaryScale (j : ℕ) : ℚ :=
  4 * (4 / 3 : ℚ) ^ j

theorem bankOrdinaryScale_pos (j : ℕ) :
    0 < bankOrdinaryScale j := by
  unfold bankOrdinaryScale
  positivity

theorem bankOrdinaryScale_succ (j : ℕ) :
    bankOrdinaryScale (j + 1) = 4 * bankOrdinaryScale j / 3 := by
  unfold bankOrdinaryScale
  rw [pow_succ]
  ring

/-- Literal membership in the marker interval
`I_Q = (4n/(3Q), 3n/(2Q)]`, written without division. -/
def InOrdinaryBankMarkerInterval (n : ℕ) (Q : ℚ) (P : ℕ) : Prop :=
  4 * (n : ℚ) < 3 * Q * (P : ℚ) ∧
    2 * Q * (P : ℚ) ≤ 3 * (n : ℚ)

/-- The full cofactor window `[4Q/3, 3Q/2]` allowed by the two legal
lower-factor states. -/
def InOrdinaryBankDonorWindow (Q : ℚ) (u : ℕ) : Prop :=
  4 * Q ≤ 3 * (u : ℚ) ∧
    2 * (u : ℚ) ≤ 3 * Q





/-- One actual ordinary-bank marker--donor pair at endpoint `M`. -/
def IsOrdinaryBankEligiblePair
    (n M : ℕ) (Q : ℚ) (pair : ℕ × ℕ) : Prop :=
  0 < Q ∧
    pair.1.Prime ∧
    0 < pair.2 ∧
    InOrdinaryBankMarkerInterval n Q pair.1 ∧
    InOrdinaryBankDonorWindow Q pair.2 ∧
    pair.2 ∈ Nat.smoothNumbers (yNat n + 1) ∧
    2 * n < pair.1 * pair.2 ∧
    pair.1 * pair.2 ≤ M



/-- A common finite ambient box.  Product eligibility makes both coordinate
bounds redundant, but retaining the box keeps the relations computational
finsets. -/
def ordinaryBankPairBox (M : ℕ) : Finset (ℕ × ℕ) :=
  Finset.Icc 1 M ×ˢ Finset.Icc 1 M

/-- The actual finite marker--donor relation at rational scale `Q`. -/
def bankOrdinaryEligibleRelation
    (n M : ℕ) (Q : ℚ) : Finset (ℕ × ℕ) :=
  by
    classical
    exact (ordinaryBankPairBox M).filter (IsOrdinaryBankEligiblePair n M Q)















/-! ## The five exceptional fixed donors -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryCorePaths -/
section


/-!
# Actual terminating ordinary-bank core paths

This file turns the large-core rule and the certified fifteen-row small table
into one deterministic finite path.  Sources `6,...,22` use the displayed
table, sources above `22` use `largeCoreStep`, and `5` is absorbing.  The
resulting finite source set is the literal set of ordinary component requests
made by one path.

The rational geometric grid is indexed here as well.  Minimality of the index
puts every source in its unique grid cell.  The finite small part contributes
at most seventeen sources at any scale, while the two-step contraction gives
the sharp bound two at every grid scale above the small table.
-/

namespace Erdos390.WholePaper

open scoped BigOperators

noncomputable section

/-! ## One deterministic descent step -/

/-- The target in the displayed small table, with an irrelevant predecessor
fallback away from the certified non-power sources. -/
def bankSmallCoreStep : ℕ → ℕ
  | 6 => 5
  | 7 => 6
  | 9 => 7
  | 10 => 9
  | 11 => 9
  | 12 => 10
  | 13 => 11
  | 14 => 12
  | 15 => 12
  | 17 => 14
  | 18 => 15
  | 19 => 15
  | 20 => 15
  | 21 => 17
  | 22 => 18
  | q => q - 1

/-- The actual ordinary-core transition.  The terminal core `5` is absorbing,
the literal small table is used through `22`, and all larger sources use the
large-core rule. -/
def bankOrdinaryCoreStep (q : ℕ) : ℕ :=
  if q ≤ 5 then 5
  else if q ≤ 22 then bankSmallCoreStep q
  else largeCoreStep q



theorem bankOrdinaryCoreStep_eq_largeCoreStep
    {q : ℕ} (hq : 22 < q) :
    bankOrdinaryCoreStep q = largeCoreStep q := by
  rw [bankOrdinaryCoreStep, if_neg (by omega), if_neg (by omega)]







theorem bankOrdinaryCoreStep_lt_self
    {q : ℕ} (hq : 5 < q) :
    bankOrdinaryCoreStep q < q := by
  by_cases hq22 : q ≤ 22
  · interval_cases q <;> simp_all [bankOrdinaryCoreStep, bankSmallCoreStep]
  · rw [bankOrdinaryCoreStep_eq_largeCoreStep (by omega)]
    exact largeCoreStep_lt_self (by omega)

/-! ## Exact indexing of the rational geometric grid -/

theorem bankOrdinaryScale_nat_add_four_le (j : ℕ) :
    (j : ℚ) + 4 ≤ bankOrdinaryScale j := by
  induction j with
  | zero => norm_num [bankOrdinaryScale]
  | succ j ih =>
      rw [bankOrdinaryScale_succ]
      have hscale : (4 : ℚ) ≤ bankOrdinaryScale j := by
        linarith
      push_cast
      linarith

 theorem bankOrdinaryScaleIndex_exists (q : ℕ) :
    ∃ j : ℕ, (q : ℚ) ≤ 4 * bankOrdinaryScale j / 3 := by
  refine ⟨q, ?_⟩
  have hlarge := bankOrdinaryScale_nat_add_four_le q
  have hpos := bankOrdinaryScale_pos q
  push_cast at hlarge
  linarith

/-- The least grid index whose upper cell endpoint contains `q`. -/
def bankOrdinaryScaleIndex (q : ℕ) : ℕ :=
  Nat.find (bankOrdinaryScaleIndex_exists q)















/-! ## The scale and certificate carried by every component -/

/-- The natural grid indices `1,...,5` corresponding to the five constructors
of `SmallDescentScale`. -/
def smallDescentScaleIndex : SmallDescentScale → ℕ
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4
  | .five => 5







/-- The grid label attached to the component leaving `q`. -/
def bankOrdinaryComponentScaleIndex (q : ℕ) : ℕ :=
  if q ≤ 22 then smallDescentScaleIndex (smallDescentScaleForSource q)
  else bankOrdinaryScaleIndex q



/-- The complete local certificate needed by an actual ordinary-bank
component. -/
def IsBankOrdinaryCoreComponent (q b : ℕ) : Prop :=
  6 ≤ q ∧
    ¬ IsPowerOfTwo q ∧
    ¬ IsPowerOfTwo b ∧
    5 ≤ b ∧
    b < q ∧
    b = bankOrdinaryCoreStep q ∧
    InGeometricDescentCell
      (bankOrdinaryScale (bankOrdinaryComponentScaleIndex q)) q b





/-! ## A literal finite terminating path -/



/-- Actual nonterminal sources traversed by the same path. -/
def bankOrdinaryCoreSources (q : ℕ) : Finset ℕ :=
  if q ≤ 5 then ∅
  else insert q (bankOrdinaryCoreSources (bankOrdinaryCoreStep q))
termination_by q
decreasing_by
  exact bankOrdinaryCoreStep_lt_self (by omega)























/-! ## The actual finite path telescopes -/

/-- Sum of the valuation changes over the actual finite source set. -/
def bankOrdinaryFinitePathChange (q : ℕ) : BankVector ℕ :=
  ∑ s ∈ bankOrdinaryCoreSources q,
    factorMoveChange s (bankOrdinaryCoreStep s)















 instance decidableCoreInGeometricCellLocal (Q : ℚ) (q : ℕ) :
    Decidable (CoreInGeometricCell Q q) := by
  unfold CoreInGeometricCell
  infer_instance







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryConcreteDemand -/
section


/-!
# Concrete ordinary-component requests and their demand

For every signed rounding slot, this file materializes one request for every
nonterminal source of its actual core path.  A request is routed by its exact
geometric-grid index and by the sign of the slot.  The request fibers are
finite sigma types, not cardinality placeholders.

The path congestion bounds give `17 * sum beta` at each small scale and the
sharp `2 * sum beta` at every large scale.  Finally the already audited
`O(yNat)` beta reserve is compared with the worst ordinary marker scale
`(n/log n)/yNat`; this is the uniform little-o estimate required by all moving
grid scales `Q <= yNat`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-- One ordinary pool is a geometric-grid index and a path orientation. -/
abbrev BankOrdinaryOrientationPool := ℕ × BankBottomOrientation

/-- One literal request: a signed beta copy and one actual nonterminal source
on the deterministic path belonging to its prime. -/
abbrev BankOrdinaryPaperRequest (n : ℕ) :=
  Σ slot : SignedBankSlot (bankRoundingBetaOnSupport n),
    ↑(bankOrdinaryCoreSources slot.1.1)

/-- The complete finite ordinary request family. -/
def bankOrdinaryPaperRequests (n : ℕ) :
    Finset (BankOrdinaryPaperRequest n) :=
  Finset.univ

def bankOrdinaryPaperRequestSource
    {n : ℕ} (request : BankOrdinaryPaperRequest n) : ℕ :=
  request.2.1

def bankOrdinaryPaperRequestTarget
    {n : ℕ} (request : BankOrdinaryPaperRequest n) : ℕ :=
  bankOrdinaryCoreStep (bankOrdinaryPaperRequestSource request)

/-- Literal routing by the component's grid scale and the signed-copy
orientation. -/
def bankOrdinaryPaperRequestPool
    (n : ℕ) (request : BankOrdinaryPaperRequest n) :
    BankOrdinaryOrientationPool :=
  (bankOrdinaryComponentScaleIndex
      (bankOrdinaryPaperRequestSource request),
    bankSignedSlotOrientation request.1)

def bankOrdinaryRequestsInPool
    (n : ℕ) (pool : BankOrdinaryOrientationPool) :
    Finset (BankOrdinaryPaperRequest n) :=
  (bankOrdinaryPaperRequests n).filter fun request ↦
    bankOrdinaryPaperRequestPool n request = pool







/-! ## Exact request-fiber cardinality -/

















/-! ## The beta reserve against the worst moving ordinary scale -/



















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryPoolMatching -/
section


/-!
# Actual matching of ordinary requests to marker--donor pairs

At every grid scale the selected marker--donor pairs are split by
`BankMarkerDonorCombinatorics` into the two path orientations.  The marker
intervals of distinct geometric scales are disjoint, so these are genuinely
disjoint pools of numerical pairs, not merely scale-tagged copies.

The beta-demand estimates are compared with the large moving marker lower
bound and the five fixed small-scale marker lower bounds.  Pointwise finite
embeddings then give one globally injective assignment from every actual
ordinary component request to an actual eligible marker--donor pair.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Actual oriented occurrence pools -/

/-- One half of the actual chosen marker--donor pairs at the prescribed grid
scale. -/
def bankOrdinaryAvailablePairs
    (n M : ℕ) (pool : BankOrdinaryOrientationPool) : Finset (ℕ × ℕ) :=
  match pool.2 with
  | .downward =>
      bankOrientationPoolFirst
        (bankOrdinaryEligibleRelation n M (bankOrdinaryScale pool.1))
  | .upward =>
      bankOrientationPoolSecond
        (bankOrdinaryEligibleRelation n M (bankOrdinaryScale pool.1))













/-! ## Capacity from the beta reserve -/











/-! ## Finite poolwise matching -/

/-- A matching is an actual embedding of every request fiber into its actual
oriented marker--donor pool. -/
structure BankOrdinaryPoolMatching
    (n M : ℕ) where
  toEmbedding : (pool : BankOrdinaryOrientationPool) →
    ↑(bankOrdinaryRequestsInPool n pool) ↪
      ↑(bankOrdinaryAvailablePairs n M pool)



def bankOrdinaryRequestInItsPool
    {n : ℕ} (request : ↑(bankOrdinaryPaperRequests n)) :
    ↑(bankOrdinaryRequestsInPool n
      (bankOrdinaryPaperRequestPool n request.1)) :=
  ⟨request.1, Finset.mem_filter.mpr ⟨request.property, rfl⟩⟩

abbrev BankOrdinaryLabeledRequest (n : ℕ) :=
  Σ pool : BankOrdinaryOrientationPool,
    ↑(bankOrdinaryRequestsInPool n pool)

def bankOrdinaryLabelRequest
    {n : ℕ} (request : ↑(bankOrdinaryPaperRequests n)) :
    BankOrdinaryLabeledRequest n :=
  ⟨bankOrdinaryPaperRequestPool n request.1,
    bankOrdinaryRequestInItsPool request⟩



def BankOrdinaryPoolMatching.slotOfLabeledRequest
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : BankOrdinaryLabeledRequest n) : ℕ × ℕ :=
  (matching.toEmbedding request.1 request.2).1





def BankOrdinaryPoolMatching.matchedPair
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ × ℕ :=
  matching.slotOfLabeledRequest (bankOrdinaryLabelRequest request)









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











/-- The actual ordinary component has exactly three interval occurrences.
The bare prime marker is deliberately not an occurrence: it is smaller than
the interval endpoint and is retained separately as bookkeeping data. -/
inductive BankOrdinaryPaperOccurrenceKind where
  | sourceState
  | targetState
  | donor
  deriving DecidableEq, Fintype

/-! ## Arithmetic helpers for rough signatures -/









/-! ## Marker injectivity inherited from the orientation pools -/



def BankOrdinaryPoolMatching.matchedMarker
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  (matching.matchedPair request).1

def BankOrdinaryPoolMatching.matchedDonorCore
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  (matching.matchedPair request).2



/-! ## The public realization object and its actual factors -/

/-- An ordinary realization packages the actual matching together with the
two elementary endpoint-range hypotheses used by every component. -/
structure BankOrdinaryPaperRealization (n M : ℕ) where
  matching : BankOrdinaryPoolMatching n M
  one_le_n : 1 ≤ n
  two_mul_n_le_M : 2 * n ≤ M

namespace BankOrdinaryPaperRealization

def marker {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  R.matching.matchedMarker request

def donorCore {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  R.matching.matchedDonorCore request

def markerDonorPair {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ × ℕ :=
  (R.marker request, R.donorCore request)























def sourceStateValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  R.marker request * bankOrdinaryPaperRequestSource request.1

def targetStateValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  R.marker request * bankOrdinaryPaperRequestTarget request.1

def donorValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  R.marker request * R.donorCore request

















/-- The finite set of all ordinary markers used by this realization. -/
def markers
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M) : Finset ℕ :=
  Finset.univ.image R.marker







 theorem exists_request_for_marker
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (P : ↑R.markers) :
    ∃ request : ↑(bankOrdinaryPaperRequests n),
      R.marker request = P.1 := by
  simpa only [markers, Finset.mem_image, Finset.mem_univ, true_and] using
    P.property

/-- The unique request carrying a marker from `R.markers`. -/
def requestForMarker
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (P : ↑R.markers) : ↑(bankOrdinaryPaperRequests n) :=
  Classical.choose (R.exists_request_for_marker P)













/-! ## The three actual occurrences and global collision-freedom -/









def occurrenceCofactor
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    BankOrdinaryPaperOccurrenceKind → ℕ
  | .sourceState => bankOrdinaryPaperRequestSource request.1
  | .targetState => bankOrdinaryPaperRequestTarget request.1
  | .donor => R.donorCore request

def occurrenceValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n))
    (kind : BankOrdinaryPaperOccurrenceKind) : ℕ :=
  R.marker request * R.occurrenceCofactor request kind















def componentOccurrences
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : Finset ℕ :=
  Finset.univ.image (R.occurrenceValue request)











/-! ## Realized component and signed-slot changes -/



def fromStateValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  match (bankOrdinaryPaperRequestPool n request.1).2 with
  | .downward => R.sourceStateValue request
  | .upward => R.targetStateValue request

def toStateValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : ℕ :=
  match (bankOrdinaryPaperRequestPool n request.1).2 with
  | .downward => R.targetStateValue request
  | .upward => R.sourceStateValue request

def realizedComponentChange
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) : BankVector ℕ :=
  factorMoveChange (R.fromStateValue request) (R.toStateValue request)



def requestOfSource
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (source : ↑(bankOrdinaryCoreSources slot.1.1)) :
    ↑(bankOrdinaryPaperRequests n) :=
  ⟨⟨slot, source⟩, Finset.mem_univ _⟩

def realizedSlotChange
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) : BankVector ℕ :=
  ∑ source : ↑(bankOrdinaryCoreSources slot.1.1),
    R.realizedComponentChange (requestOfSource slot source)

def signedFinitePathChange
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    BankVector ℕ :=
  match slot.2 with
  | .inl _copy => bankOrdinaryFinitePathChange slot.1.1
  | .inr _copy => -bankOrdinaryFinitePathChange slot.1.1



def signedPrimeToFiveChange
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    BankVector ℕ :=
  match slot.2 with
  | .inl _copy => coordinateUnit 5 - coordinateUnit slot.1.1
  | .inr _copy => coordinateUnit slot.1.1 - coordinateUnit 5



end BankOrdinaryPaperRealization

/-! ## Eventual realized allocation -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperComponents -/
section


/-!
# Combined bottom and ordinary bank realization

This file is only the composition layer.  The two allocation mechanisms stay
independent, but their marker ranges are strictly separated:

`3 * ordinaryMarker < n < 3 * bottomMarker`.

Consequently the marker maps remain injective after the two request families
are joined.  Prime-marker recovery also turns this strict separation into
cross-family disjointness of the actual state/donor occurrence sets.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-- The joint marker-request type: relevant bottom components on the left and
all ordinary path components on the right. -/
abbrev BankPaperMarkerRequest (n : ℕ) :=
  ↑(bankBottomRelevantPaperRequests n) ⊕
    ↑(bankOrdinaryPaperRequests n)

/-- A complete bank realization, with the eventual local geometry retained
as fields because it is precisely what cross-family marker recovery uses. -/
structure BankPaperRealization (n M : ℕ) where
  bottom : BankBottomPaperRealization n M
  ordinary : BankOrdinaryPaperRealization n M
  six_le_yNat : 6 ≤ yNat n
  three_mul_yNat_le_n : 3 * yNat n ≤ n

namespace BankPaperRealization







def ordinaryMarkers
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  R.ordinary.markers

def bottomMarkers
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  R.bottom.relevantMarkers

def allMarkers
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  R.ordinaryMarkers ∪ R.bottomMarkers





/-! ## Cross-family actual occurrence disjointness -/





/-- The union of all ordinary actual component occurrences. -/
def ordinaryComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  (bankOrdinaryPaperRequests n).attach.biUnion
    (fun request ↦ R.ordinary.componentOccurrences request)

def bottomComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  R.bottom.relevantComponentOccurrences

def allComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  R.ordinaryComponentOccurrences ∪ R.bottomComponentOccurrences







end BankPaperRealization

/-! ## Terminal combined realization -/



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

/-- The least exponent `k` for which `n < 2^k * B`, written using the
ceiling logarithm.  The intended use has `0 < B`. -/
def promotionExponent (n B : ℕ) : ℕ :=
  Nat.clog 2 (n / B + 1)

/-- A block promoted into the central interval by a power of two. -/
def promotedBlock (n B : ℕ) : ℕ :=
  2 ^ promotionExponent n B * B













/-- The full `p`-primary block in the central binomial coefficient. -/
def centralPrimeBlock (n p : ℕ) : ℕ :=
  p ^ (Nat.choose (2 * n) n).factorization p









/-- The promoted factor `A_p = 2^{k_p} p^{e_p}` from the paper. -/
def promotedCentralFactor (n p : ℕ) : ℕ :=
  promotedBlock n (centralPrimeBlock n p)















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.ResidualCentralFactors -/
section


/-! # The finite family of promoted residual central factors -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Central-binomial prime divisors at or below the residual cutoff. -/
def residualCentralPrimes (n X : ℕ) : Finset ℕ :=
  (Nat.choose (2 * n) n).primeFactors.filter (fun p ↦ p ≤ X)

/-- The set of their promoted factors. -/
def residualPromotedFactors (n X : ℕ) : Finset ℕ :=
  (residualCentralPrimes n X).image (promotedCentralFactor n)

/-- Total extra power of two introduced by residual promotion. -/
def residualPromotionCost (n X : ℕ) : ℕ :=
  ∑ p ∈ residualCentralPrimes n X,
    promotionExponent n (centralPrimeBlock n p)















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

/-- Central-binomial prime divisors strictly above the residual cutoff. -/
def largeCentralPrimes (n X : ℕ) : Finset ℕ :=
  (Nat.choose (2 * n) n).primeFactors.filter (fun p ↦ X < p)















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

/-- A cofactor follows either the row-zero route or one stationary carry
row, including the exact allowed cofactor interval. -/
def IsRoutedCentralCofactor (n p q : ℕ) : Prop :=
  (n < p ∧ p ≤ 2 * n ∧ q = 1) ∨
    ∃ r : ℕ, 1 ≤ r ∧ r = n / p ∧
      p ∈ stationaryPrimeLayer n r ∧ r + 1 ≤ q ∧ q ≤ 2 * r + 1

/-- A simultaneous choice of routed cofactors for all central primes above
the cutoff. -/
def IsLargeCentralCofactorChoice
    (n X : ℕ) (q : ℕ → ℕ) : Prop :=
  ∀ p ∈ largeCentralPrimes n X, IsRoutedCentralCofactor n p (q p)







/-- The actual marker--cofactor factor. -/
def largeCentralAnchor (q : ℕ → ℕ) (p : ℕ) : ℕ := p * q p

/-- All large marker factors, as an honest finite set. -/
def largeCentralAnchors (n X : ℕ) (q : ℕ → ℕ) : Finset ℕ :=
  (largeCentralPrimes n X).image (largeCentralAnchor q)

/-- The exact product of all chosen cofactors. -/
def largeCentralCofactorProduct (n X : ℕ) (q : ℕ → ℕ) : ℕ :=
  (largeCentralPrimes n X).prod q













/-- The union of promoted low blocks and routed large marker factors. -/
def fullCentralAnchors (n X : ℕ) (q : ℕ → ℕ) : Finset ℕ :=
  residualPromotedFactors n X ∪ largeCentralAnchors n X q

/-- Promotion powers of two together with all chosen large cofactors. -/
def centralAnchorDivisor (n X : ℕ) (q : ℕ → ℕ) : ℕ :=
  2 ^ residualPromotionCost n X * largeCentralCofactorProduct n X q









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.UpperTailValuationAsymptotic -/
section


/-!
# Fixed-prime upper-tail valuation asymptotics

The paper's tail has length `ceil (c n / log n)` above `2n`.  The exact
integer two-sided Legendre bounds squeeze its valuation at every fixed prime.
The logarithmic remainder is discharged by `UpperScale`; no valuation limit
is assumed as an input.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

/-- The actual `p`-adic valuation contributed by the factorial tail
`(2n, 2n + upperTailLength c n]`. -/
def upperTailValuation (c : ℝ) (n p : ℕ) : ℕ :=
  (upperEndpoint n (upperTailLength c n)).factorial.factorization p -
    (2 * n).factorial.factorization p

















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

/-- The literal product of all integers in `(2n,2n+h]`. -/
def centralTailProduct (n h : ℕ) : ℕ :=
  (factorInterval (2 * n) (2 * n + h)).prod id















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







/-- The fixed finite set of primes up to a natural bound. -/
def primesUpTo (B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter Nat.Prime









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

/-- The paper's fixed-`R` central-anchor cutoff `X_R^{anc}`. -/
def centralAnchorCutoff (R n : ℕ) : ℕ :=
  n / (R + 1)

/-- One explicit threshold sufficient for both cutoff separations. -/
def centralAnchorCutoffThreshold (R : ℕ) : ℕ :=
  4 * (R + 1) ^ 2















































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificateData -/
section


/-!
# The explicit finite allocation certificate

This file is deliberately only data.  It is the 211-entry rational array from
`reference/numerical_verifier.py`, transcribed literally so that the Lean
kernel, rather than the Python program, can check every calculation used by
the finite allocation lemma.
-/

namespace Erdos390.WholePaper

/-- One nonzero coordinate of the finite allocation certificate. -/
structure AllocationEntry where
  row : ℕ
  cofactor : ℕ
  numerator : ℕ
  denominator : ℕ
deriving DecidableEq, Repr

namespace AllocationEntry







end AllocationEntry

open AllocationEntry





















end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificateChecker -/
section


/-!
# Small exact-checker primitives for the finite allocation certificate

The arithmetic facts are compiled in several bounded modules.  Keeping the
shared definitions here lets each module reduce only its own small batch.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

open AllocationEntry

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal range, positivity, and denominator conditions on one entry. -/
def AllocationEntry.Valid (e : AllocationEntry) : Prop :=
  1 ≤ e.row ∧ e.row ≤ 200 ∧
    e.row + 1 ≤ e.cofactor ∧ e.cofactor ≤ 2 * e.row + 1 ∧
      0 < e.numerator ∧ 0 < e.denominator

instance instDecidableAllocationEntryValid (e : AllocationEntry) :
    Decidable e.Valid := by
  unfold AllocationEntry.Valid
  infer_instance

/-- An unreduced nonnegative fraction checked by natural-number arithmetic. -/
structure RawFraction where
  numerator : ℕ
  denominator : ℕ
deriving DecidableEq, Repr

namespace RawFraction











def CrossEq (a b : RawFraction) : Prop :=
  a.numerator * b.denominator = b.numerator * a.denominator

def CrossLE (a b : RawFraction) : Prop :=
  a.numerator * b.denominator ≤ b.numerator * a.denominator

instance instDecidableCrossEq (a b : RawFraction) : Decidable (a.CrossEq b) := by
  unfold CrossEq
  infer_instance

instance instDecidableCrossLE (a b : RawFraction) : Decidable (a.CrossLE b) := by
  unfold CrossLE
  infer_instance

end RawFraction















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

/-- The complete central-anchor object after guarding a finite set of bank
markers.  The last field exposes the exact cofactor-level collision guard at
every changed marker. -/
structure GuardedCentralAnchorCertificate
    (c : ℝ) (R n : ℕ) (left right : ℕ → ℕ)
    (changed : Finset ℕ) where
  q : ℕ → ℕ
  anchors : Finset ℕ
  isCofactorChoice :
    IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q
  anchors_eq :
    anchors = fullCentralAnchors n (centralAnchorCutoff R n) q
  anchors_subset : anchors ⊆ Finset.Ioc n (2 * n)
  anchors_prod :
    anchors.prod id = Nat.choose (2 * n) n *
      centralAnchorDivisor n (centralAnchorCutoff R n) q
  divisor_prime_support :
    ∀ ℓ : ℕ, ℓ.Prime →
      ℓ ∣ centralAnchorDivisor n (centralAnchorCutoff R n) q →
        ℓ ∈ primesUpTo (2 * R + 1)
  divisor_reserve :
    ∀ ℓ ∈ primesUpTo (2 * R + 1),
      (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
            secondOrderScale n +
          ((centralAnchorDivisor n
            (centralAnchorCutoff R n) q).factorization ℓ : ℝ) ≤
        (upperTailValuation c n ℓ : ℝ)
  divisor_dvd_tail :
    centralAnchorDivisor n (centralAnchorCutoff R n) q ∣
      centralTailProduct n (upperTailLength c n)
  guarded_incident_cores :
    ∀ p ∈ changed,
      q p ≠ left p ∧ q p ≠ right p



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperAnchorGuards -/
section


/-!
# Actual bank markers as central-anchor guards

This is the finite composition layer between the realized bank components
and the guarded central-cofactor construction.  The set of changed markers
is literally the intersection of the realized bank marker set with the
large-central-prime set.  Its two forbidden cores are recovered from the
unique incident component.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

namespace BankPaperRealization

/-- The two incident state cores attached to a realized bank marker.  The
ordinary and bottom branches are disjoint; the final branch is irrelevant
outside `allMarkers` and merely makes the function total. -/
def anchorGuardIncidentCores
    {n M : ℕ} (R : BankPaperRealization n M) (p : ℕ) : ℕ × ℕ :=
  if hpOrdinary : p ∈ R.ordinary.markers then
    let request := R.ordinary.requestForMarker ⟨p, hpOrdinary⟩
    (bankOrdinaryPaperRequestSource request.1,
      bankOrdinaryPaperRequestTarget request.1)
  else if hpBottom : p ∈ R.bottom.relevantMarkers then
    R.bottom.relevantMarkerIncidentStateCores ⟨p, hpBottom⟩
  else (0, 0)

def anchorGuardLeftCore
    {n M : ℕ} (R : BankPaperRealization n M) (p : ℕ) : ℕ :=
  (R.anchorGuardIncidentCores p).1

def anchorGuardRightCore
    {n M : ℕ} (R : BankPaperRealization n M) (p : ℕ) : ℕ :=
  (R.anchorGuardIncidentCores p).2

/-- Exactly the realized bank markers which actually occur in the large
central divisor. -/
def centralChangedMarkers
    {n M : ℕ} (R : BankPaperRealization n M) (depth : ℕ) : Finset ℕ :=
  R.allMarkers ∩ largeCentralPrimes n (centralAnchorCutoff depth n)

















end BankPaperRealization

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

/-- The two state endpoints of a precharged component. -/
inductive BankPaperPrechargeEndpoint where
  | base
  | alternate
  deriving DecidableEq, Fintype

namespace BankBottomPaperRealization



end BankBottomPaperRealization

namespace BankPaperRealization

local instance bankPaperMarkerRequestDecidableEq (n : ℕ) :
    DecidableEq (BankPaperMarkerRequest n) :=
  Classical.decEq _

/-! ## Global component data -/

/-- Orientation-aware state occupied before the component move. -/
def prechargeBaseStateValue
    {n M : ℕ} (R : BankPaperRealization n M) :
    BankPaperMarkerRequest n → ℕ
  | .inl request =>
      R.bottom.fromStateValue
        (bankBottomRelevantRequestToPaperRequest request)
  | .inr request => R.ordinary.fromStateValue request





/-- The actual state/donor occurrences belonging to a component.  Bottom
terminal rows retain donor=upper as one `Finset` occurrence. -/
def prechargeComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M) :
    BankPaperMarkerRequest n → Finset ℕ
  | .inl request =>
      R.bottom.componentOccurrences
        (bankBottomRelevantRequestToPaperRequest request)
  | .inr request => R.ordinary.componentOccurrences request

















/-! ## Complete rough signatures -/







/-! ## Endpoint and donor injectivity -/





















/-! ## Literal finite states, donor tail, and replacement map -/

def prechargeBaseState
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  indexedPathState R.prechargeBaseStateValue















































/-! ## Component counts and the base product -/

def prechargeBaseStateProduct
    {n M : ℕ} (R : BankPaperRealization n M) : ℕ :=
  R.prechargeBaseState.prod id





















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPaths -/
section


/-!
# Actual full bank paths

For one signed rounding slot, the component index is the disjoint union of
the ordinary `p→5` sources and the relevant truncated bottom rows.  Each
index contributes exactly one state-zero endpoint and one state-one endpoint;
markers and donors belong to the component census, but never to either path
state.  Global occurrence disjointness makes both endpoint maps injective.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Actual component indices of one full signed bank path. -/
abbrev BankPaperPathComponent
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :=
  ↑(bankOrdinaryCoreSources slot.1.1) ⊕
    ↑(bankBottomRelevantMoves slot.1.1)

/-- The full rectangular-family request belonging to a slot and bottom row. -/
def bankPaperBottomRequestOfMove
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (move : ↑(bankBottomRelevantMoves slot.1.1)) :
    ↑(bankBottomPaperRequests n) :=
  ⟨(slot, move.1), Finset.mem_univ _⟩

/-- The same request with its path relevance retained in the type. -/
def bankPaperBottomRelevantRequestOfMove
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (move : ↑(bankBottomRelevantMoves slot.1.1)) :
    ↑(bankBottomRelevantPaperRequests n) :=
  ⟨(slot, move.1), by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [bankBottomPaperRequestRelevant_iff_mem_moves]
    simpa only [bankBottomPaperRequestPrime] using move.property⟩



/-- Embed a path component into the globally injective marker-request type. -/
def bankPaperPathComponentRequest
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    BankPaperPathComponent slot → BankPaperMarkerRequest n
  | .inl source =>
      .inr (BankOrdinaryPaperRealization.requestOfSource slot source)
  | .inr move =>
      .inl (bankPaperBottomRelevantRequestOfMove slot move)



namespace BankPaperRealization

/-- The three actual occurrences carried by one component index.  Terminal
bottom rows may have only two distinct values because donor and upper state
coincide. -/
def pathComponentOccurrences
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    BankPaperPathComponent slot → Finset ℕ
  | .inl source => R.ordinary.componentOccurrences
      (BankOrdinaryPaperRealization.requestOfSource slot source)
  | .inr move => R.bottom.componentOccurrences
      (bankPaperBottomRequestOfMove slot move)

/-- State zero is the source side of a downward path and the target side of
its reversed path. -/
def pathStateZeroValue
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    BankPaperPathComponent slot → ℕ
  | .inl source => R.ordinary.fromStateValue
      (BankOrdinaryPaperRealization.requestOfSource slot source)
  | .inr move => R.bottom.fromStateValue
      (bankPaperBottomRequestOfMove slot move)

/-- State one is the opposite endpoint in every realized component. -/
def pathStateOneValue
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    BankPaperPathComponent slot → ℕ
  | .inl source => R.ordinary.toStateValue
      (BankOrdinaryPaperRealization.requestOfSource slot source)
  | .inr move => R.bottom.toStateValue
      (bankPaperBottomRequestOfMove slot move)













/-- The two actual path states.  Each contains one endpoint per component and
contains neither bare markers nor donor-only occurrences. -/
def pathStateZero
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) : Finset ℕ :=
  indexedPathState (R.pathStateZeroValue slot)

def pathStateOne
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) : Finset ℕ :=
  indexedPathState (R.pathStateOneValue slot)

/-- The full actual component census, including states and donors but no bare
marker. -/
def pathComponentCensus
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) : Finset ℕ :=
  Finset.univ.biUnion (R.pathComponentOccurrences slot)















/-- Actual valuation change of the complete realized path. -/
def realizedFullPathChange
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) : BankVector ℕ :=
  ∑ component : BankPaperPathComponent slot,
    factorMoveChange (R.pathStateZeroValue slot component)
      (R.pathStateOneValue slot component)



/-- Uniform signed unit represented by a full path: downward slots contribute
`-e_p`, and reversed slots contribute `+e_p`. -/
def signedFullPathChange
    {n : ℕ} (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    BankVector ℕ :=
  match slot.2 with
  | .inl _copy => -coordinateUnit slot.1.1
  | .inr _copy => coordinateUnit slot.1.1



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.FloatingRoundingStep -/
section


/-!
# One rank-deficient floating-rounding step

This file isolates the linear-algebra move used in the paper's floating
rounding lemma.  If fewer equations than fractional coordinates are being
retained, one may preserve every retained equation, keep all coordinates in
`[0,1]`, freeze every already integral coordinate, and make at least one new
coordinate integral.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Coordinates strictly between the two integral boundary values. -/
def fractionalSupport {A : Type*} [Fintype A] (x : A → ℝ) : Finset A := by
  classical
  exact Finset.univ.filter fun a ↦ x a ≠ 0 ∧ x a ≠ 1







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.FloatingRoundingCounts -/
section


/-!
# Counting retained equations in floating rounding

The paper retains active row equations and columns meeting more than `4*d`
currently fractional coordinates.  These elementary double-counts show that
their total number is strictly smaller than the number of fractional
coordinates, which is the hypothesis of `exists_floating_step`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

def activeRows {A R : Type*} [Fintype A] [Fintype R]
    (F : Finset A) (row : A → R) : Finset R := by
  classical
  exact F.image row

def rowFiber {A R : Type*} [Fintype A]
    (F : Finset A) (row : A → R) (r : R) : Finset A := by
  classical
  exact F.filter fun a ↦ row a = r

def columnSupportIn {A C : Type*} [Fintype A]
    (F : Finset A) (inc : C → A → Prop) (c : C) : Finset A := by
  classical
  exact F.filter fun a ↦ inc c a

def columnsContaining {A C : Type*} [Fintype C]
    (H : Finset C) (inc : C → A → Prop) (a : A) : Finset C := by
  classical
  exact H.filter fun c ↦ inc c a

def heavyColumns {A C : Type*} [Fintype A] [Fintype C]
    (F : Finset A) (inc : C → A → Prop) (d : ℕ) : Finset C := by
  classical
  exact Finset.univ.filter fun c ↦
    4 * d < (columnSupportIn F inc c).card



















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.FloatingRoundingRows -/
section


/-!
# Integer row sums force two fractional coordinates

After integral coordinates are frozen, an active row cannot contain exactly
one fractional coordinate: the whole row sum is an integer and every other
entry is zero or one.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

def rowSet {A R : Type*} [Fintype A]
    (row : A → R) (r : R) : Finset A := by
  classical
  exact Finset.univ.filter fun a ↦ row a = r







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.FloatingRoundingDiscrepancy -/
section


/-!
# Discrepancy after a column becomes light

Once a column has at most `4*d` still-fractional coordinates, every later
change is supported on those coordinates and has magnitude at most one per
coordinate.  This is the final estimate in the paper's floating-rounding
argument.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

def zeroOneColumn {A C : Type*} (inc : C → A → Prop) (c : C) (a : A) : ℝ := by
  classical
  exact if inc c a then 1 else 0



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.PrimePowerColumns -/
section


/-!
# Prime-power columns for floating rounding

The columns used in the paper are indexed by prime powers `p^j ≤ M`.  A
positive integer `a ≤ M` belongs to exactly one column for each prime-factor
occurrence, and hence to at most `Nat.log 2 M` columns.
-/

namespace Erdos390.WholePaper

noncomputable section

def primePowerColumns (M : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 2 M).product (Finset.Icc 1 M)).filter fun q ↦
    q.1.Prime ∧ q.1 ^ q.2 ≤ M

@[simp]
theorem mem_primePowerColumns {M p j : ℕ} :
    (p, j) ∈ primePowerColumns M ↔
      2 ≤ p ∧ p ≤ M ∧ 1 ≤ j ∧ j ≤ M ∧ p.Prime ∧ p ^ j ≤ M := by
  classical
  simp [primePowerColumns, and_assoc, and_left_comm, and_comm]

def primePowerInc (M : ℕ) (q : ↥(primePowerColumns M)) (a : ℕ) : Prop :=
  q.1.1 ^ q.1.2 ∣ a

def divisorPrimePowerPairs (a : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact a.primeFactors.biUnion fun p ↦
    (Finset.Icc 1 (a.factorization p)).image fun j ↦ (p, j)









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.ValuationError -/
section


/-!
# From prime-power column discrepancy to valuation error

Summing the prime-power columns belonging to a fixed prime `p` recovers the
`p`-adic valuation.  Thus a `4*d` error per column gives the paper's bound
`4*d * floor(log_p M)`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

def primeExponentRange (p M : ℕ) : Finset ℕ :=
  Finset.Icc 1 (Nat.log p M)

def roundingValuationError {A : Type*} [Fintype A]
    (value : A → ℕ) (X x : A → ℝ) (p : ℕ) : ℝ :=
  ∑ a, (X a - x a) * (value a).factorization p



/-- The admissible global column attached to an exponent in
`primeExponentRange p M`. -/
def primePowerColumnOf {p M : ℕ} (hp : p.Prime) (hM : 0 < M)
    (j : ↥(primeExponentRange p M)) : ↥(primePowerColumns M) := by
  have hj : 1 ≤ j.1 := (Finset.mem_Icc.mp j.2).1
  have hjlog : j.1 ≤ Nat.log p M := (Finset.mem_Icc.mp j.2).2
  have hpow : p ^ j.1 ≤ M := Nat.pow_le_of_le_log hM.ne' hjlog
  have hp_le_pow : p ≤ p ^ j.1 := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right hp.pos hj
  exact ⟨(p, j.1), mem_primePowerColumns.mpr
    ⟨hp.two_le, hp_le_pow.trans hpow, hj,
      hjlog.trans (Nat.log_le_self p M), hp, hpow⟩⟩







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.GuardedExactificationAlgebra -/
section


/-!
# Finite algebra for guarded integral exactification

This file contains only finite constructions.  A concrete two-sided bank has
one positive and one negative family of `β p` slots at every explicit
coordinate `p`.  Given a vector in the `β`-box, the toggled slots are the
first required copies in the corresponding families.  No bank-existence,
capacity, donor, or collision assertion is introduced here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The integral coordinates selected by a zero-one real vector. -/
def integralSelection {A : Type*} [Fintype A] (X : A → ℝ) : Finset A := by
  classical
  exact Finset.univ.filter fun a ↦ X a = 1

/-- The literal set of selected integer factors. -/
def selectedFactorSet {A : Type*} [Fintype A]
    (value : A → ℕ) (X : A → ℝ) : Finset ℕ :=
  (integralSelection X).image value

/-- Union of one explicitly chosen state from every concrete path slot. -/
def chosenBankFactors {G : Type*} [Fintype G]
    (state : G → Bool → Finset ℕ) (choice : G → Bool) : Finset ℕ := by
  classical
  exact Finset.univ.biUnion fun g ↦ state g (choice g)

/-- The state-zero bank is a special chosen-state union. -/
def baseBankFactors {G : Type*} [Fintype G]
    (state : G → Bool → Finset ℕ) : Finset ℕ :=
  chosenBankFactors state fun _ ↦ false

























/-- Integer rounded-minus-fractional valuation error, expressed only with
actual selected products and the charged base/target factorizations. -/
def integralRoundingError {A : Type*} [Fintype A]
    (value : A → ℕ) (X : A → ℝ) (B₀ Y q : ℕ) : ℤ :=
  (((selectedFactorSet value X).prod id).factorization q : ℤ) +
    (B₀.factorization q : ℤ) - (Y.factorization q : ℤ)







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.GuardedExactificationProduct -/
section


/-!
# Guarded unions and their ordinary products

Every hypothesis below names literal finite factor sets.  In particular,
the guard conclusions do not pass through a separate compatibility
contract.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The literal union used after rounding and bank-state replacement. -/
def guardedFinalFactorSet {A G : Type*} [Fintype A] [Fintype G]
    (fixed : Finset ℕ) (state : G → Bool → Finset ℕ)
    (choice : G → Bool) (value : A → ℕ) (X : A → ℝ) : Finset ℕ :=
  (fixed ∪ chosenBankFactors state choice) ∪ selectedFactorSet value X











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperExactificationState -/
section


/-!
# The actual paper bank as a two-state exactification bank

`BankPaperPaths` orients a downward slot from state zero to state one, so its
change is `-e_p`; the generic exactification interface instead calls the
left-hand signed family `+e_p`.  We therefore pair each generic slot with the
actual slot of the opposite orientation.  Boolean state `false` remains the
paper's precharged path state zero and state `true` remains path state one.
This simultaneously aligns signs and keeps the base product equal to the
one reserved in the tail.  The file proves the required product change,
complete-row invariance, positivity, and pairwise cross-slot disjointness.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Swap the two copies with the same prime and copy index. -/
def bankPaperOppositeSlot {P : Type*} {beta : P → ℕ} :
    SignedBankSlot beta → SignedBankSlot beta
  | ⟨p, .inl copy⟩ => ⟨p, .inr copy⟩
  | ⟨p, .inr copy⟩ => ⟨p, .inl copy⟩









/-- Boolean state convention used by `guarded_integral_exactification`.
The opposite-orientation reindexing aligns signs while state `false` is still
the literal precharged base state. -/
def BankPaperRealization.exactificationState
    {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (selected : Bool) : Finset ℕ :=
  if selected then R.pathStateOne (bankPaperOppositeSlot slot)
  else R.pathStateZero (bankPaperOppositeSlot slot)







namespace BankPaperRealization



















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrechargeExactificationBridge -/
section


/-!
# Identification of the precharged state with the exactification base bank

The concrete precharge layer indexes components by the global request type,
whereas guarded exactification takes the union of state zero over signed bank
slots.  These are two presentations of the same finite set.  The opposite-slot
reindexing used to align signed valuation changes is an involution, so it does
not alter the global state-zero union.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Forget the outer signed-slot index of a dependent path component and
recover its globally unique paper request. -/
def bankPaperIndexedPathComponentRequest {n : ℕ} :
    (Σ slot : SignedBankSlot (bankRoundingBetaOnSupport n),
      BankPaperPathComponent slot) → BankPaperMarkerRequest n
  | ⟨slot, component⟩ => bankPaperPathComponentRequest slot component



namespace BankPaperRealization











end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrechargedTailTarget -/
section


/-!
# The residual target after the guarded anchor charge

This file names the exact natural-number target passed to fractional
selection and guarded exactification.  Combined divisibility of the guarded
anchor divisor and the precharged bank immediately shows that the generic
exactification base product divides this target.  The final multiplication
identity is division-free.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace GuardedCentralAnchorCertificate

/-- The literal factorial-tail quotient remaining after charging the guarded
central-anchor divisor. -/
def prechargedTailTarget
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) : ℕ :=
  centralTailProduct n (upperTailLength c n) /
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q









end GuardedCentralAnchorCertificate

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperSelectorTailTarget -/
section


/-!
# The residual selector target after all base charges

The guarded central anchors are charged before `prechargedTailTarget` is
formed.  Fractional selection starts only after an independently fixed
factor set and the literal state-zero exactification bank have also been
charged.  This file names that second quotient and records the exact
division-free and valuation interfaces used by the post-tangent
certificate.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-- The complete factor product already present before fractional selector
weights are introduced: the caller's fixed factors and the actual
state-zero exactification bank. -/
def selectorTailCharge
    {n M : ℕ} (R : BankPaperRealization n M)
    (fixed : Finset ℕ) : ℕ :=
  fixed.prod id * (baseBankFactors R.exactificationState).prod id





end BankPaperRealization

namespace GuardedCentralAnchorCertificate

/-- The natural-number product left for fractional selection after the
central anchors, fixed factors, and actual base exactification bank have all
been charged. -/
def selectorTailTarget
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset ℕ) : ℕ :=
  certificate.prechargedTailTarget / R.selectorTailCharge fixed









end GuardedCentralAnchorCertificate

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CompleteRoughRowPartition -/
section


/-!
# The finite partition into complete rough rows

For a finite set `A`, its complete rough labels are precisely the labels
actually attained on `A`.  Filtering `A` at one such label gives the
corresponding row.  These rows form a literal finite partition of `A`:
they are nonempty, lie in `A`, have constant complete signature, are
pairwise disjoint, and have union exactly `A`.

The final results transport arbitrary additive weights across this
partition, including the factorization-coordinate weights used later in
the paper.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Labels and row fibers -/

/-- The finite set of complete rough labels attained by elements of `A`. -/
def completeRoughLabelSet (y : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.image (completeRoughLabel y)

/-- The fiber in `A` carrying one specified complete rough label. -/
def completeRoughRowFiber
    (y : ℕ) (A : Finset ℕ) (label : ℕ) : Finset ℕ :=
  A.filter (fun a ↦ completeRoughLabel y a = label)

@[simp]
theorem mem_completeRoughLabelSet
    {y label : ℕ} {A : Finset ℕ} :
    label ∈ completeRoughLabelSet y A ↔
      ∃ a ∈ A, completeRoughLabel y a = label := by
  simp [completeRoughLabelSet]





/-! ## Row support and constancy -/









/-! ## Exact finite partition -/





/-! ## Additive partition identities -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperGuardedUpperProductAssembly -/
section


/-!
# Final guarded upper-product assembly for the concrete paper bank

The residual complement selection returned by exactification is the union of
its genuinely fixed factors, the chosen paper-bank state, and the selected
candidate factors.  The guarded central anchors remain a fourth, external
family.  This file joins that external family to the exactified residual set
and exposes exactly the two missing cross-family guards:

* anchors versus the exactification-fixed factors;
* anchors versus the selected candidates (or, more uniformly, their whole
  candidate universe).

Anchor versus bank-state disjointness is discharged by the concrete guarded
collision theorem.  The remaining product input is also kept literal:
exactification supplies `residual.prod = Y`, while the caller must still
supply `Y * centralAnchorDivisor = centralTailProduct`.  No quotient or
unstated disjointness is manufactured here.
-/

namespace Erdos390.WholePaper

noncomputable section

namespace BankPaperRealization

/-- The complete residual complement selection produced after Boolean bank
replacement and integral candidate selection. -/
def exactificationResidualFactorSet
    {A : Type*} [Fintype A] {n M : ℕ}
    (R : BankPaperRealization n M) (fixed : Finset ℕ)
    (positive negative : ↑(bankRoundingPrimeSupport n) → ℕ)
    (value : A → ℕ) (X : A → ℝ) : Finset ℕ :=
  guardedFinalFactorSet fixed R.exactificationState
    (signedBankStateChoice positive negative) value X



/-! ## The two genuinely missing anchor guards -/







/-! ## Interval and product assembly -/









/-! ## Expanded final bundle -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CanonicalCompleteRoughRows -/
section


/-!
# Canonical complete rough rows for exactification

A finite candidate set itself supplies the coordinate type used by floating
rounding.  Its attained complete rough labels supply a canonical finite row
type.  The row signature is simply factorization of the label; positivity
of attained labels and uniqueness of factorization make this signature map
injective.

This file also identifies `rowSet` with the literal complete-rough fiber and
provides the value, interval, summation, and row-integrality bridges required
by the exactification interface.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Canonical finite types and maps -/

/-- The canonical candidate type associated with the finite set `A`. -/
abbrev CompleteRoughCandidate (A : Finset ℕ) := ↥A

/-- The canonical finite row type: precisely the complete rough labels
attained on `A`. -/
abbrev CanonicalCompleteRoughRow (y : ℕ) (A : Finset ℕ) :=
  ↥(completeRoughLabelSet y A)

/-- Send a candidate to the row indexed by its complete rough label. -/
def canonicalCompleteRoughRow
    (y : ℕ) (A : Finset ℕ) :
    CompleteRoughCandidate A → CanonicalCompleteRoughRow y A :=
  fun a ↦ ⟨completeRoughLabel y a.1,
    mem_completeRoughLabelSet.mpr ⟨a.1, a.2, rfl⟩⟩

/-- The signature attached to a canonical row is the factorization of its
integer label. -/
def canonicalCompleteRoughRowSignature
    (y : ℕ) (A : Finset ℕ) :
    CanonicalCompleteRoughRow y A → ℕ →₀ ℕ :=
  fun row ↦ row.1.factorization

/-- The candidate value passed to exactification is its underlying natural
number. -/
def canonicalCompleteRoughCandidateValue
    (A : Finset ℕ) : CompleteRoughCandidate A → ℕ :=
  fun a ↦ a.1









/-! ## Signature and value interfaces -/











/-! ## Literal subtype fibers and `rowSet` -/











/-! ## Summation and integrality bridges -/











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSaiasUpperReduction -/
section


/-!
# Forward canonical Saias-to-upper-construction reduction

The weighted HT--Saias development and the canonical upper-construction
terminal deliberately live on opposite sides of the still-missing selector
and tangent-flow argument.  Merely importing both modules would not connect
them.  This file gives the honest forward reduction.

For every active complete-rough row, the endpoint envelope and the three
displayed paper-scale ledger inequalities imply the literal raw-row quota
bound.  A separate selector handoff must turn that family of bounds into an
actual feasible, row-integral, valuation-exact post-tangent selector.  Only
then is the existing canonical upper-construction theorem invoked.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Exact finite output required after the analytic row estimates have been
consumed by the still-separate selector and tangent-flow construction.  This
contains precisely the three `x`-dependent premises of
`bankPaper_isAdmissibleEndpoint_of_canonicalPostTangentCertificate`; all
geometric and collision premises stay outside the structure. -/
structure BankPaperCanonicalPostTangentOutput
    {c : ℝ} {depth n : ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (candidates fixed : Finset ℕ) where
  selector : ℕ → ℝ
  feasible : ∀ a ∈ candidates,
    0 ≤ selector a ∧ selector a ≤ 1
  rowIntegral :
    ∀ label ∈ completeRoughLabelSet (yNat n) candidates,
      ∃ k : ℤ,
        ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          selector a = (k : ℝ)
  valuationCertificate : ∀ q,
    ((fixed.prod id *
        (baseBankFactors R.exactificationState).prod id).factorization q : ℝ) +
        ∑ a ∈ candidates,
          selector a * (a.factorization q : ℝ) =
      ((certificate.prechargedTailTarget).factorization q : ℝ)



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentCollisionCounting -/
section


/-!
# Counting the tangent collision events

This file is the finite counting layer immediately before the local-lemma
module.  It does three things which are kept separate in the paper's prose.

* It proves that the product of the request-wise uniform laws is the uniform
  law on the finite dependent product.  Consequently an actual collision
  probability is exactly

  `number of colliding configurations / number of all configurations`.

* A two-request collision is covered by the four literal endpoint equations.
  For prime endpoint labels, the equation `p*a=q*b` has at most
  `N/p+1` solutions when `p=q`, and at most `N/(p*q)+1` solutions when
  `p != q`, provided the left endpoint is at most `N`.

* The incident-event sum for one request is reindexed exactly by all other
  requests.  A pairwise cardinality/counting estimate can therefore be
  summed using the two endpoint-label loads of the fixed request and the
  total request count.

No collision-free choice and no bound on a collision probability are assumed
here.  In the clean-list terminal the remaining inputs are request-wise list
cardinality lower bounds and an explicit arithmetic comparison of the finite
counting budget with the paper's shared-label and disjoint-label charges.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal

namespace Erdos390.WholePaper

noncomputable section

/-! ## The product law is uniform -/















/-! ## Exact collision configurations -/









/-! ## Naming the two requests and the four endpoint equations -/











/-- The two choices of endpoint on one request. -/
inductive TangentEndpointSide
  | source
  | target
  deriving DecidableEq, Fintype











/-! ## Raw solutions of `p*a=q*b` -/

























/-! ## From list cardinalities to pair probabilities -/









/-! ## Exact reindexing of an incident-event sum -/























/-! ## Request loads and the literal `1/8` terminal -/

/-- Whether a request has a specified endpoint label. -/
def tangentRequestHasLabel
    {Request : Type*} (source target : Request → ℕ)
    (label : ℕ) (request : Request) : Prop :=
  source request = label ∨ target request = label

instance instDecidableTangentRequestHasLabel
    {Request : Type*} (source target : Request → ℕ)
    (label : ℕ) (request : Request) :
    Decidable (tangentRequestHasLabel source target label request) := by
  unfold tangentRequestHasLabel
  infer_instance



























/-! ## Specialization to the actual clean common lists -/















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalUpperConstructionEventually -/
section


/-!
# Eventual canonical upper construction from a post-tangent continuation

The precharge-capacity stage already constructs, eventually, the paper bank,
the guarded central-anchor certificate, and the three exact divisibility and
product facts for the precharged tail.  The theorem below consumes those
witnesses and discharges all numerical cutoff conditions by existing
eventual estimates.

No selector or tangent existence is asserted here.  Instead, one explicit
continuation supplies the remaining finite candidate set, feasible weights,
integral complete-rough row sums, residual selector valuation identity, and
collision guards after seeing the actual capacity-stage witnesses.  The
residual identity is stated for `selectorTailTarget`; its charged form is
derived here before applying the canonical exactification reduction.
-/

open scoped BigOperators
open Filter

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- The exact post-tangent continuation still needed after the capacity
stage has fixed `depth`.  It may depend on the actual endpoint, bank, guarded
anchor certificate, and all three capacity-stage facts. -/
def BankPaperCanonicalPostTangentContinuationAtDepth
    (c : ℝ) (depth : ℕ) : Prop :=
  (∀ᶠ n : ℕ in atTop,
      ∃ R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)),
        ∃ certificate : GuardedCentralAnchorCertificate c depth n
            R.anchorGuardLeftCore R.anchorGuardRightCore
            (R.centralChangedMarkers depth),
          centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q * R.prechargeBaseStateProduct ∣
              centralTailProduct n (upperTailLength c n) ∧
            (baseBankFactors R.exactificationState).prod id ∣
              certificate.prechargedTailTarget ∧
            certificate.prechargedTailTarget *
                centralAnchorDivisor n (centralAnchorCutoff depth n)
                  certificate.q =
              centralTailProduct n (upperTailLength c n)) →
    ∀ᶠ n : ℕ in atTop,
      ∃ R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)),
        ∃ certificate : GuardedCentralAnchorCertificate c depth n
            R.anchorGuardLeftCore R.anchorGuardRightCore
            (R.centralChangedMarkers depth),
          centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q * R.prechargeBaseStateProduct ∣
              centralTailProduct n (upperTailLength c n) ∧
            (baseBankFactors R.exactificationState).prod id ∣
              certificate.prechargedTailTarget ∧
            certificate.prechargedTailTarget *
                centralAnchorDivisor n (centralAnchorCutoff depth n)
                  certificate.q =
              centralTailProduct n (upperTailLength c n) ∧
            ∃ candidates : Finset ℕ, ∃ x : ℕ → ℝ,
              ∃ fixed : Finset ℕ,
                candidates ⊆
                    factorInterval n
                      (upperEndpoint n (upperTailLength c n)) ∧
                fixed ⊆
                    factorInterval n
                      (upperEndpoint n (upperTailLength c n)) ∧
                (∀ a ∈ candidates, 0 ≤ x a ∧ x a ≤ 1) ∧
                (∀ label ∈ completeRoughLabelSet (yNat n) candidates,
                  ∃ k : ℤ,
                    ∑ a ∈ completeRoughRowFiber
                        (yNat n) candidates label, x a = (k : ℝ)) ∧
                R.selectorTailCharge fixed ∣
                  certificate.prechargedTailTarget ∧
                (∀ q,
                  ∑ a ∈ candidates,
                      x a * (a.factorization q : ℝ) =
                    ((certificate.selectorTailTarget R fixed).factorization q :
                      ℝ)) ∧
                Disjoint fixed candidates ∧
                (∀ slot selected,
                  Disjoint fixed (R.exactificationState slot selected)) ∧
                (∀ slot selected,
                  Disjoint candidates
                    (R.exactificationState slot selected)) ∧
                Disjoint certificate.anchors fixed ∧
                Disjoint certificate.anchors candidates







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalFixedDepthCapacityBridge -/
section


/-!
# Fixed-depth capacity bridge to the main reduction

The capacity-aware main reduction names one depth chosen by
`exists_depth_bankPaper_f_le_upperEndpoint_of_canonicalPostTangentContinuation`.
The depth-first combined-charge terminal chooses a depth independently.
There is no reason for those two witnesses to be equal.

This file removes the need for such an equality.  It exposes the literal
capacity premise at an arbitrary fixed depth, proves the upper-endpoint
reduction at that same depth, and observes that
`BankPaperCombinedChargeTerminalAtDepth` already contains exactly those
capacity facts.  Consequently the depth selected by the depth-first charge
theorem can be passed directly to the main reduction.
-/

open scoped BigOperators
open Filter

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## The exact capacity premise at a fixed depth -/

/-- The three eventual capacity facts consumed by
`BankPaperCanonicalPostTangentContinuationAtDepth`, with the depth kept as
an explicit input rather than selected existentially. -/
def BankPaperCanonicalCapacityAtDepth
    (c : ℝ) (depth : ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∃ bank : BankPaperRealization n
        (upperEndpoint n (upperTailLength c n)),
      ∃ certificate : GuardedCentralAnchorCertificate c depth n
          bank.anchorGuardLeftCore bank.anchorGuardRightCore
          (bank.centralChangedMarkers depth),
        centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q * bank.prechargeBaseStateProduct ∣
            centralTailProduct n (upperTailLength c n) ∧
          (baseBankFactors bank.exactificationState).prod id ∣
            certificate.prechargedTailTarget ∧
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n)



/-! ## Same-depth upper-endpoint reduction -/





/-! ## The depth-first witness carries its own upper bridge -/



/-! ## Direct main reductions with the depth-first quantifier order -/





end

end Erdos390.WholePaper

end


