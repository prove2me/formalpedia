-- Prove2me | Definitions.Def_erdos390_analytic_foundations_006
-- name    : erdos390_analytic_foundations_006
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T14:57:56.433171+00:00
-- url     : https://prove2.me/theorems/c59073c4-5f4e-4bf1-af5a-824b233a13db
-- title:
--   Rough-row selectors, Saias normalization and finite bank allocation data
-- statement:
--   This bundle defines varying-active-mass baselines, rough and smooth row geometry, head-compatible raw selectors, reduced-residue intervals, the Saias endpoint normal form and approximation predicates, row-correction pools, smooth quota/height quantities, bank donor windows, and the finite allocation tables and checking interfaces used by the anchor construction.
--
--   Let $P_W$ be the product of the head primes, and let $H$ and $B$ denote the high and broad lower blocks for natural parameters $(n,h,K)$. For real parameters $\alpha,\beta,\ell$, the raw selector is
--   $$w(a)=\mathbf1_{\gcd(a,P_W)=1}\left(\alpha\mathbf1_H(a)+\frac\beta\ell\mathbf1_B(a)\right).$$
--   Its complete-rough-row mass is obtained by summing over the appropriate rough-label fibre. The balanced choice of $\alpha$ is defined from the head density, tail height and broad-block contribution, with natural-number subtraction retained in the block lengths.
--
--   The Saias definitions distinguish the normal-form main term, endpoint error and the predicate demanding a uniform approximation through logarithmic coordinate five. Together with explicit finite donor/allocation data, these definitions connect the analytic rough-row estimates to the later bank-capacity and central-anchor constructions.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughHeadCompatibleFinitePoint.lean; grouped definitions extracted from multiple source modules at this commit, including Erdos390.Full.PaperCanonicalActiveMassBaseline, Erdos390.Full.PaperProposition87ActiveMassTransport, Erdos390.WholePaper.BankPaperCanonicalP87VaryingMassUniformOrderConnector, with the remaining originating modules identified by source-module comments in the definition body.

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_005


/- Source module: Erdos390.Full.PaperCanonicalActiveMassBaseline -/
section


/-!
# Literal-active-mass variant of the canonical barycentric baseline

`BarycentricTarget.baseline` is the normalized probability allocation used
throughout the existing covariance chain.  The paper's actual bridge uses
the same normalized cell law with total mass `q_n`, generally of order
`n / log n`.  This backward-compatible module supplies that scaled
allocation without changing `BarycentricTarget` or any existing theorem
signature.
-/

open scoped BigOperators

namespace Erdos390.Full

open PaperGuardCensus PaperBridgeFit

noncomputable section

namespace PaperGuardCensus.BarycentricTarget

variable {Head : Type*} [Fintype Head] [Nonempty Head]
  {D : StructuredSampleData Head} (T : BarycentricTarget D)

/-- The literal unnormalized baseline with total active mass `q_n`. -/
def activeMassBaseline (q : Real) (hq : 0 < q) : BaselineAllocation D where
  cellMass := fun c => q * T.cellProbability c
  cellMass_pos := fun c => mul_pos hq (T.cellProbability_pos c)

omit [Nonempty Head] in
/-- Scaling changes the total mass from one to the supplied `q_n`. -/
theorem activeMassBaseline_totalMass (q : Real) (hq : 0 < q) :
    (T.activeMassBaseline q hq).totalMass = q := by
  unfold activeMassBaseline BaselineAllocation.totalMass
  rw [← Finset.mul_sum, T.sum_cellProbability, mul_one]



omit [Nonempty Head] in
/-- Coordinate weights are scaled by exactly the same active-mass factor. -/
theorem activeMassBaseline_baseWeight
    (q : Real) (hq : 0 < q) (m : D.Sample) :
    (T.activeMassBaseline q hq).baseWeight m =
      q * T.baseline.baseWeight m := by
  unfold BaselineAllocation.baseWeight activeMassBaseline baseline
  ring





end PaperGuardCensus.BarycentricTarget

namespace PaperBridgeFit.BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band] [Nonempty Head]
  (B : BridgeData Head Band)

omit [Nonempty Head] in
/-- A `BridgeData` using the scaled canonical allocation has literal active
mass `q_n`, rather than the normalization artifact `1`. -/
theorem q_eq_of_baseline_eq_activeMassBaseline
    (T : BarycentricTarget B.sampleData)
    (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq) :
    B.q = q := by
  unfold BridgeData.q
  rw [hbaseline, T.activeMassBaseline_totalMass q hq]





end PaperBridgeFit.BridgeData

end


end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperProposition87ActiveMassTransport -/
section


/-!
# Homogeneous active-mass transport for Proposition 8.7

The canonical covariance argument is an argument about the normalized cell
law.  The literal bridge, however, has total active mass `q_n`, not one.
This file makes the homogeneity exact without changing any of the existing
Proposition 8.7 interfaces.

For a bridge whose baseline is `T.activeMassBaseline q hq`, we form the
mass-one companion with the same sample, partition, gauge, reference head,
and scale, and with baseline `T.baseline`.  We prove that

* the two tilted probability laws and normalized covariances agree;
* every active weight and raw paper moment for the literal bridge is `q`
  times its companion value;
* after dividing the requested raw moment increment by `q`, the two ODE
  vector fields agree exactly, including at points where the globally
  defined inverse is the zero fallback; and
* a companion Proposition 8.7 path therefore transports to a literal
  `q`-mass path.  Feasibility is proved afresh with the literal frozen and
  active ledgers, so protected frozen mass may overlap an active coordinate.

No equality between the literal baseline and the old mass-one baseline is
assumed.
-/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open PaperGuardCensus

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The mass-one companion of a literal active-mass bridge.  All arithmetic,
gauge, and scale data are retained definitionally; only the baseline is
replaced by the canonical probability allocation. -/
def normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) : BridgeData Head Band where
  sampleData := B.sampleData
  baseline := T.baseline
  partition := B.partition
  lowBand := B.lowBand
  referenceHead := B.referenceHead
  w := B.w
  w_pos := B.w_pos
  n_gt_one := B.n_gt_one

@[simp] theorem normalizedLawCompanion_sampleData
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).sampleData = B.sampleData :=
  rfl

@[simp] theorem normalizedLawCompanion_baseline
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).baseline = T.baseline :=
  rfl

@[simp] theorem normalizedLawCompanion_partition
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).partition = B.partition :=
  rfl

@[simp] theorem normalizedLawCompanion_lowBand
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).lowBand = B.lowBand :=
  rfl

@[simp] theorem normalizedLawCompanion_referenceHead
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).referenceHead = B.referenceHead :=
  rfl

@[simp] theorem normalizedLawCompanion_w
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).w = B.w :=
  rfl

@[simp] theorem normalizedLawCompanion_L
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).L = B.L :=
  rfl

@[simp] theorem normalizedLawCompanion_q [Nonempty Head]
    (T : BarycentricTarget B.sampleData) :
    (B.normalizedLawCompanion T).q = 1 := by
  exact T.baseline_totalMass

















































end BridgeData

open ArithmeticModel PaperGuardCensus PaperPermittedRegularMesh
open RegularMeshPrimeCutoffs



namespace BridgeData



end BridgeData

/-!
## Varying paper mass

The paper uses `q_n`, not a fixed `q`.  Uniformity is retained once
`1 <= q_n`: the normalized companion ledger is bounded by
`(Cactive / q_n) / L <= Cactive / L`, so no ODE radius, mesh constant, or
eventual threshold needs to depend on `q_n`.
-/



namespace BridgeData



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalP87VaryingMassUniformOrderConnector -/
section


/-!
# Uniform paper order for varying-mass canonical Proposition 8.7

The varying-active-mass Proposition 8.7 theorem is uniform in the mass
family once that family is eventually at least one.  Its original public
statement, however, takes the family before exposing the mesh threshold and
the prime cutoff, so that logical statement does not record the uniform
dependency order.

This connector exposes `meshTol` and `W0` first.  Only after a width
`W ≥ W0` has been selected is the varying family `qMass` introduced.  The
proof uses the mass-one literal theorem to select the two uniform cutoffs,
then repeats the normalized-law transport used by
`canonical_proposition87_varyingActiveMassLiteralBandBalance`.
-/

open Filter Topology
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperBridgeFit.BridgeData
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperPermittedRegularMesh
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-- Quantifier-uniform form of the varying-active-mass literal Proposition
8.7 statement.  The mesh tolerance and prime cutoff are selected before
both the final width and the varying active-mass family. -/
def BankPaperCanonicalP87VaryingMassUniformOrderStatement
    (cMesh : Real)
    (I : PhysicalIntervals) (U : Real)
    (Cprom Cbank : Nat) (ledger : ∀ n, Ledger n Cprom Cbank) : Prop :=
  0 < cMesh →
  1 ≤ U →
  (∀ sigma, 1 ≤ I.lower sigma) →
  (∀ sigma, I.upper sigma ≤ U) →
  ∃ meshTol : Real, 0 < meshTol ∧
  ∃ W0 : Nat, ∀ W : Nat, W0 ≤ W →
    ∀ (qMass : Nat → Real),
      (∀ᶠ n : Nat in atTop, 1 ≤ qMass n) →
    ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
      (Phead : Head → HeadPattern.Pattern),
    (∀ h : Head, ∀ p : Nat,
      p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
    ∀ (Ctarget Cinitial Cmass Cfixed Cactive marginFloor : Real),
      0 ≤ Ctarget → 0 ≤ Cinitial → 0 ≤ Cmass →
      0 ≤ Cfixed → 0 ≤ Cactive → 0 < marginFloor →
    ∃ radius : NNReal, 0 < (radius : Real) ∧
    ∃ Cpost : Real, 0 ≤ Cpost ∧
    ∀ {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
      (hdelta : 0 < delta)
      (_hPermitted : IsPermitted (cMesh := cMesh) M),
      delta + eta ≤ meshTol →
      ∀ᶠ n : Nat in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n → B.sampleData.W = W →
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                hsep hremaining) →
            (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition =
                RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta B.n_gt_one hWne S) →
            (hscale : B.w = delta + eta) →
            ∀ (T : BarycentricTarget B.sampleData)
              (hq : 0 < qMass B.sampleData.n),
              marginFloor ≤ T.cellMassMargin →
              B.baseline =
                T.activeMassBaseline (qMass B.sampleData.n) hq →
            ∀ (Delta : Fin (M.cellCount + 1) → Real),
              B.HasTargetEnvelopes Ctarget Delta →
            ∀ (markedTarget : Nat → Real) (N : Real),
              0 ≤ N →
              B.q ≤ Cmass * N →
              (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
                abs (markedTarget p -
                  B.paperMoment (B.markedValuation p) 0) ≤
                    Cinitial * N / ((p : Real) * B.L)) →
              (∀ j,
                Delta j = B.markedBandResidual markedTarget 0 j) →
            ∀ {Fixed : Type*} [Fintype Fixed]
              (fixedValue : Fixed → Nat) (fixedWeight : Fixed → Real)
              (quota : Int),
              (quota : Real) = (∑ f, fixedWeight f) + B.q →
              B.sampleData.HeadPatternsSeparated →
              (∀ x,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∈
                  Set.Icc (0 : Real) 1) →
              (∀ m : B.sampleData.Sample,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight
                  (B.sampleData.value m) ≤ Cfixed / B.L) →
              (∀ m : B.sampleData.Sample,
                B.baseline.baseWeight m ≤ Cactive / B.L) →
              B.HasPaperProposition87Conclusion
                Delta radius markedTarget N Cpost
                  fixedValue fixedWeight quota



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



/-- Coordinate description of the complete rough signature. -/
theorem completeRoughSignature_apply (y a p : ℕ) :
    completeRoughSignature y a p =
      if y < p then a.factorization p else 0 := rfl



 theorem completeRoughSignature_support_prime (y a : ℕ) :
    ∀ p : ℕ, p ∈ (completeRoughSignature y a).support → p.Prime := by
  intro p hp
  rw [Finsupp.mem_support_iff] at hp
  have hpCut : y < p := by
    by_contra hcut
    simp [completeRoughSignature, hcut] at hp
  have hpValue : a.factorization p ≠ 0 := by
    simpa [completeRoughSignature, Finsupp.filter_apply, hpCut] using hp
  have hpSupport : p ∈ a.factorization.support :=
    Finsupp.mem_support_iff.mpr hpValue
  exact Nat.prime_of_mem_primeFactors (by
    simpa only [Nat.support_factorization] using hpSupport)

/-- Factoring the integer rough label recovers the complete vector
signature exactly. -/
theorem completeRoughLabel_factorization (y a : ℕ) :
    (completeRoughLabel y a).factorization = completeRoughSignature y a := by
  exact Nat.prod_pow_factorization_eq_self
    (completeRoughSignature_support_prime y a)

/-- Vector and integer conventions partition factors into exactly the same
rough rows. -/
theorem completeRoughSignature_eq_iff_label_eq {y a b : ℕ} :
    completeRoughSignature y a = completeRoughSignature y b ↔
      completeRoughLabel y a = completeRoughLabel y b := by
  constructor
  · intro h
    exact congrArg (fun s : ℕ →₀ ℕ ↦ s.prod (fun p e ↦ p ^ e)) h
  · intro h
    have hfactorization := congrArg Nat.factorization h
    simpa only [completeRoughLabel_factorization] using hfactorization



/-- Number of factors in a finite state having one specified integer rough
label. -/
def completeLabelMultiplicity
    (y : ℕ) (state : Finset ℕ) (label : ℕ) : ℕ :=
  (state.filter (fun a ↦ completeRoughLabel y a = label)).card

















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







@[simp]
theorem mem_completeRoughRowFiber
    {y label a : ℕ} {A : Finset ℕ} :
    a ∈ completeRoughRowFiber y A label ↔
      a ∈ A ∧ completeRoughLabel y a = label := by
  simp [completeRoughRowFiber]



/-! ## Row support and constancy -/









/-! ## Exact finite partition -/





/-! ## Additive partition identities -/









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

/-- The moving layer in Section 3.  Its four inequalities are the exact
integer forms of
`M/(2r+2) < p ≤ M/(2r+1)` and `n/(r+1) < p ≤ n/r`. -/
def movingPrimeLayer (n M r : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter fun p =>
    p.Prime ∧
      M < (2 * r + 2) * p ∧
      (2 * r + 1) * p ≤ M ∧
      n < (r + 1) * p ∧
      r * p ≤ n

@[simp] theorem mem_movingPrimeLayer {n M r p : ℕ} :
    p ∈ movingPrimeLayer n M r ↔
      p ≤ M ∧ p.Prime ∧
        M < (2 * r + 2) * p ∧
        (2 * r + 1) * p ≤ M ∧
        n < (r + 1) * p ∧
        r * p ≤ n := by
  simp only [movingPrimeLayer, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff]













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.Constants -/
section


/-!
# Exact constants for Sections 3 and 4

This file records the thirteen lower-bound row masses, the nine small
primes, and the exact rational value of the paper's constant.  The same row
mass is used by the cofactor allocation in Section 4.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The mass of allocation/lower-bound row `r`:
`alpha_r = 1 / ((r+1)(2r+1))`. -/
def alpha (r : ℕ) : ℚ :=
  1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1))

/-- The small-prime set used by the first thirteen lower-bound layers. -/
def smallPrimes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23}

/-- The total mass in the first thirteen rows. -/
def A13 : ℚ :=
  ∑ r ∈ Finset.Icc 1 13, alpha r

/-- The total valuation capacity of the small-prime set. -/
def S23 : ℚ :=
  ∑ ℓ ∈ smallPrimes, 1 / (((ℓ - 1 : ℕ) : ℚ))

/-- The exact rational form of the paper's second-order constant. -/
def C0Rat : ℚ :=
  A13 / S23























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.ResidualCentralFactors -/
section


/-! # The finite family of promoted residual central factors -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







theorem residualCentralPrimes_prime {n X p : ℕ}
    (hp : p ∈ residualCentralPrimes n X) : p.Prime := by
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralCarryAnchors -/
section


/-! # Exact arithmetic of the fixed-prefix central carry anchors -/

namespace Erdos390.WholePaper

noncomputable section







/-- A marker prime above the entire cofactor range is recovered uniquely
from its marker--cofactor product. -/
theorem prime_mul_cofactor_eq_iff_of_marker_large
    {X p p' q q' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (hpLarge : X < p) (hq'Pos : 0 < q') (hq'Upper : q' ≤ X) :
    p * q = p' * q' → p = p' ∧ q = q' := by
  intro hproduct
  have hpDvd : p ∣ p' * q' := by
    rw [← hproduct]
    exact dvd_mul_right p q
  rcases (hp.dvd_mul.mp hpDvd) with hpp' | hpq'
  · have hprimeEq : p = p' :=
      (Nat.prime_dvd_prime_iff_eq hp hp').mp hpp'
    subst p'
    exact ⟨rfl, Nat.mul_left_cancel hp.pos hproduct⟩
  · have hpLeQ : p ≤ q' := Nat.le_of_dvd hq'Pos hpq'
    omega

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









@[simp]
theorem mem_primesUpTo {B p : ℕ} :
    p ∈ primesUpTo B ↔ p.Prime ∧ p ≤ B := by
  simp [primesUpTo, and_comm]







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

/-- The upper tail block `E = (2n, 2n+h]`. -/
def roughUpperBlock (n h : ℕ) : Finset ℕ :=
  Finset.Ioc (2 * n) (2 * n + h)

/-- The high lower block `H = (2n-Kh, 2n]`. -/
def roughHighLowerBlock (n h K : ℕ) : Finset ℕ :=
  Finset.Ioc (2 * n - K * h) (2 * n)

/-- The broad lower block `J = (n, 2n-Kh]`. -/
def roughBroadLowerBlock (n h K : ℕ) : Finset ℕ :=
  Finset.Ioc n (2 * n - K * h)

/-- The complete raw candidate set before numerical guards. -/
def roughRawCandidateSet (n h K : ℕ) : Finset ℕ :=
  roughHighLowerBlock n h K ∪ roughBroadLowerBlock n h K

/-- The two lower physical blocks are disjoint at their common endpoint. -/
theorem roughHighLowerBlock_disjoint_roughBroadLowerBlock
    (n h K : ℕ) :
    Disjoint (roughHighLowerBlock n h K)
      (roughBroadLowerBlock n h K) := by
  rw [Finset.disjoint_left]
  intro a haHigh haBroad
  simp only [roughHighLowerBlock, roughBroadLowerBlock,
    Finset.mem_Ioc] at haHigh haBroad
  omega











/-! ## The finite head and raw weights -/

/-- The paper's head-prime product `P_hd`, with every prime `p ≤ W`. -/
def roughHeadModulus (W : ℕ) : ℕ :=
  (primesUpTo W).prod id

/-- The zero-valuation head pattern whose matches are precisely the positive
integers coprime to `roughHeadModulus W`. -/
def roughHeadZeroPattern (W : ℕ) : Erdos390.Full.HeadPattern.Pattern where
  primes := primesUpTo W
  exponent := fun _p ↦ 0
  prime_mem := fun _p hp ↦ (mem_primesUpTo.mp hp).1

@[simp]
theorem roughHeadZeroPattern_modulus (W : ℕ) :
    (roughHeadZeroPattern W).modulus = roughHeadModulus W := rfl

@[simp]
theorem roughHeadZeroPattern_factor (W : ℕ) :
    (roughHeadZeroPattern W).factor = 1 := by
  simp [roughHeadZeroPattern, Erdos390.Full.HeadPattern.Pattern.factor]



/-- The paper's fixed reduced-residue density
`delta_hd = phi(P_hd) / P_hd`. -/
def roughHeadDensity (W : ℕ) : ℝ :=
  ((roughHeadModulus W).totient : ℝ) / (roughHeadModulus W : ℝ)



/-- The literal choice
`alpha = (h / delta_hd - (beta/L) |J|) / |H|`, with the already-proved
integer lengths `|H| = K*h` and `|J| = n-K*h` written directly. -/
def roughHeadBalancedAlpha
    (W n h K : ℕ) (beta L : ℝ) : ℝ :=
  (((h : ℕ) : ℝ) / roughHeadDensity W -
      (beta / L) * (((n - K * h : ℕ) : ℝ))) /
    (((K * h : ℕ) : ℝ))





/-- Restrict an arbitrary finite set to integers coprime to the complete
head-prime product. -/
def roughHeadFree (W : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter (fun a ↦ Nat.Coprime a (roughHeadModulus W))

@[simp]
theorem mem_roughHeadFree
    {W a : ℕ} {A : Finset ℕ} :
    a ∈ roughHeadFree W A ↔
      a ∈ A ∧ Nat.Coprime a (roughHeadModulus W) := by
  simp [roughHeadFree]

/-- The indicator of membership in a finite natural-number set. -/
def roughFiniteIndicator (A : Finset ℕ) (a : ℕ) : ℝ :=
  if a ∈ A then 1 else 0

/-- The literal head-compatible raw weight from the paper. -/
def roughHeadCompatibleRawWeight
    (W n h K : ℕ) (α β L : ℝ) (a : ℕ) : ℝ :=
  if Nat.Coprime a (roughHeadModulus W) then
    α * roughFiniteIndicator (roughHighLowerBlock n h K) a +
      (β / L) * roughFiniteIndicator (roughBroadLowerBlock n h K) a
  else 0

/-- The actual finite vector obtained by inserting the paper's balanced
choice of `alpha` into the raw weight and restricting its coordinate type
to the literal candidate set. -/
def roughHeadCompatibleRawPoint
    (W n h K : ℕ) (beta L : ℝ) :
    ↑(roughRawCandidateSet n h K) → ℝ :=
  fun a ↦ roughHeadCompatibleRawWeight W n h K
    (roughHeadBalancedAlpha W n h K beta L) beta L a.1

@[simp]
theorem roughHeadCompatibleRawPoint_apply
    (W n h K : ℕ) (beta L : ℝ)
    (a : ↑(roughRawCandidateSet n h K)) :
    roughHeadCompatibleRawPoint W n h K beta L a =
      roughHeadCompatibleRawWeight W n h K
        (roughHeadBalancedAlpha W n h K beta L) beta L a.1 := rfl













/-- The literal raw mass in one complete rough row. -/
def roughHeadCompatibleRawRowMass
    (W n h K y label : ℕ) (α β L : ℝ) : ℝ :=
  ∑ a ∈ completeRoughRowFiber y (roughRawCandidateSet n h K) label,
    roughHeadCompatibleRawWeight W n h K α β L a



/-! ## Exact head inclusion--exclusion and smooth physical shifts -/





/-- Head-free smooth integers in one literal half-open interval. -/
def roughHeadFreeSmoothInterval
    (W lo hi y : ℕ) : Finset ℕ :=
  roughHeadFree W (smoothInterval lo hi y)





/-- An unrestricted two-piece smooth physical block, with all integer
endpoint effects retained in the two finite cardinalities. -/
def roughSmoothPhysicalBlock
    (lo split hi y : ℕ) (α broad : ℝ) : ℝ :=
  α * ((smoothInterval split hi y).card : ℝ) +
    broad * ((smoothInterval lo split y).card : ℝ)

/-- The same physical block after imposing head coprimality. -/
def roughHeadFreeSmoothPhysicalBlock
    (W lo split hi y : ℕ) (α broad : ℝ) : ℝ :=
  α * ((roughHeadFreeSmoothInterval W split hi y).card : ℝ) +
    broad * ((roughHeadFreeSmoothInterval W lo split y).card : ℝ)



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

/-- Reduced residues in a half-open segment `[start,start+length)`. -/
def reducedResidueSegment
    (M start length : ℕ) : Finset ℕ :=
  (Finset.Ico start (start + length)).filter
    (fun a ↦ Nat.Coprime a M)

/-- Reduced residues in the paper's physical interval `(lo,hi]`. -/
def reducedResidueIoc
    (M lo hi : ℕ) : Finset ℕ :=
  (Finset.Ioc lo hi).filter (fun a ↦ Nat.Coprime a M)

/-- Integers in `(lo,hi]` which are both divisible by `D` and coprime to
the fixed modulus `M`. -/
def coprimeMultipleIoc
    (M D lo hi : ℕ) : Finset ℕ :=
  (Finset.Ioc lo hi).filter
    (fun a ↦ D ∣ a ∧ Nat.Coprime a M)

/-- The exact reduced-residue density `phi(M)/M`. -/
def fixedModulusReducedResidueDensity (M : ℕ) : ℝ :=
  (M.totient : ℝ) / (M : ℝ)

/-! ## Exact periodic decomposition -/

















/-! ## Explicit fixed-period error -/







/-! ## Exact CRT reindexing and multiplier-independent error -/







/-! ## Paper-head specializations -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughTransitionBalancedBlock -/
section


/-!
# Finite algebra for transition-complete balanced rough blocks

The first analytic estimate after constructing the head-compatible raw
point compares a finite signed collection of smooth-count endpoints.  Its
main term cancels because the signed real lengths balance exactly.  This
file isolates that deterministic layer: exact centering, the finite
Lipschitz ledger, logarithmic displacement scaling, and retention of every
endpoint error.

The final specialization is the literal four-endpoint comparison from the
paper, with relative endpoints
`(1 + κ), 1, (1 - K * κ), 1 / 2`.  No smooth-number asymptotic or
regularity estimate is packaged as data here; those remain explicit
hypotheses for the later analytic module.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## General finite balanced-block algebra -/











/-! ## The literal four physical endpoints -/



/-- Coefficients obtained by expanding
`upper block - δ * physical block` and combining equal endpoints. -/
def roughPhysicalBlockCoefficient
    (δ α β L : ℝ) : Fin 4 → ℝ :=
  ![1, -(1 + δ * α), δ * (α - β / L), δ * (β / L)]













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughBalancedFriableResidualReduction -/
section


/-!
# Residual cancellation in the balanced four-endpoint friable block

The closed de Bruijn theorem controls the endpoint residual

`R(X,y) = Psi(X,y) - X * rho(log X / log y)`

by `O(X / log y)`.  Applying that estimate independently at four
endpoints loses one logarithm.  This file avoids that lossy triangle
inequality.  It proves that the literal four-endpoint residual is exactly
two *short residual increments* plus one broad increment whose coefficient
already contains `1/L`.

It also records the exact reverse Buchstab recurrence for `R`, using one
common prime interval for both endpoints.  The remaining missing analytic
input is thereby reduced to a local regularity inequality for `R`; it is
strictly an estimate for the genuine friable counting function and contains
no selector, row, rounding, or feasibility conclusion.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The genuine endpoint residual -/

/-- The Dickman main term at one natural endpoint. -/
noncomputable def roughFriableDickmanMain (X y : ℕ) : ℝ :=
  (X : ℝ) * rho (FriableAsymptotic.dickmanU X y)

/-- The actual de Bruijn residual, not an assumed error function. -/
noncomputable def roughFriableResidual (X y : ℕ) : ℝ :=
  (FriableAsymptotic.friableCount X y : ℝ) -
    roughFriableDickmanMain X y

@[simp]
theorem roughFriableDickmanMain_zero (y : ℕ) :
    roughFriableDickmanMain 0 y = 0 := by
  simp [roughFriableDickmanMain]

@[simp]
theorem roughFriableResidual_zero (y : ℕ) :
    roughFriableResidual 0 y = 0 := by
  simp [roughFriableResidual]







/-! ## Exact reverse Buchstab recurrence for the residual -/

/-- The common prime interval `y < p <= Z` used to reverse the largest
prime-factor recurrence at every endpoint `X <= Z`. -/
def roughReversePrimeInterval (y Z : ℕ) : Finset ℕ :=
  (Z + 1).primesBelow \ (y + 1).primesBelow











/-! ## Verified regularity of the Dickman main term -/







/-! ## The literal four-endpoint residual collapse -/

/-- Natural endpoints corresponding to the paper's ordered tuple
`(X_+, X, X_-, X_{1/2})`. -/
def roughPhysicalNatEndpoint
    (Xplus X Xminus Xhalf : ℕ) : Fin 4 → ℕ :=
  ![Xplus, X, Xminus, Xhalf]

/-- The genuine four-endpoint friable combination with the exact paper
coefficients. -/
noncomputable def roughPhysicalFriableCombination
    (δ α β L : ℝ) (Xplus X Xminus Xhalf y : ℕ) : ℝ :=
  ∑ i : Fin 4,
    roughPhysicalBlockCoefficient δ α β L i *
      (FriableAsymptotic.friableCount
        (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y : ℝ)

/-- The corresponding four-endpoint Dickman main combination. -/
noncomputable def roughPhysicalDickmanCombination
    (δ α β L : ℝ) (Xplus X Xminus Xhalf y : ℕ) : ℝ :=
  ∑ i : Fin 4,
    roughPhysicalBlockCoefficient δ α β L i *
      roughFriableDickmanMain
        (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y

/-- After expanding the paper coefficients, all order-one endpoint
residuals cancel into two local increments.  Only the broad increment
remains endpointwise, and it carries the explicit coefficient `δ β/L`. -/
noncomputable def roughPhysicalResidualTransition
    (δ α β L : ℝ) (Xplus X Xminus Xhalf y : ℕ) : ℝ :=
  (roughFriableResidual Xplus y - roughFriableResidual X y) -
    δ * α *
      (roughFriableResidual X y - roughFriableResidual Xminus y) +
    δ * (β / L) *
      (roughFriableResidual Xhalf y - roughFriableResidual Xminus y)



/-! ## The one remaining analytic inequality -/







end

end Erdos390.WholePaper

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

/-- The right-continuous representative of the derivative of the finite
Dickman function, extended by zero on the open initial face.  The value at
`u = 1` is the right limit `-1`; changing one point does not change any
Lebesgue integral below. -/
noncomputable def roughSaiasDickmanDerivative (u : ℝ) : ℝ :=
  if u < 1 then 0 else -rho (u - 1) / u

/-- The fractional weight occurring after integration by parts in the
de Bruijn--Saias normalization. -/
noncomputable def roughSaiasFractionalWeight (y : ℕ) (v : ℝ) : ℝ :=
  Int.fract ((y : ℝ) ^ v) * (y : ℝ) ^ (-v)

/-- A fixed-interval version of `G_y`.  For `u <= 5`, the zero extension of
the Dickman derivative makes this equal to the paper's integral over
`[0, (u-1)_+]`; see `roughSaiasG_eq_moving` below. -/
noncomputable def roughSaiasG (y : ℕ) (u : ℝ) : ℝ :=
  rho u - ∫ v in (0 : ℝ)..5,
    roughSaiasDickmanDerivative (u - v) *
      roughSaiasFractionalWeight y v



/-- The finite normal form `z * G_y(u) - fract z`.  This definition does not
silently assert equality with the Stieltjes-integral definition of `Lambda`;
that equality is the integration-by-parts step from the cited source. -/
noncomputable def roughSaiasLambdaNormalForm (z : ℝ) (y : ℕ) : ℝ :=
  z * roughSaiasG y (Real.log z / Real.log (y : ℝ)) - Int.fract z

@[simp]
theorem roughSaiasDickmanDerivative_of_lt_one
    {u : ℝ} (hu : u < 1) :
    roughSaiasDickmanDerivative u = 0 := by
  simp [roughSaiasDickmanDerivative, hu]



@[simp]
theorem roughSaiasDickmanDerivative_one :
    roughSaiasDickmanDerivative 1 = -1 := by
  simp [roughSaiasDickmanDerivative]

















/-- The finite normal form is exactly the integer count on the initial
Dickman face.  This includes the corner `u = 1`: the only exceptional
integrand value is at the left endpoint and has zero fractional weight. -/
theorem roughSaiasG_eq_one_of_le_one {y : ℕ} {u : ℝ} (hu : u ≤ 1) :
    roughSaiasG y u = 1 := by
  have hzero :
      (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative (u - v) *
          roughSaiasFractionalWeight y v) = 0 := by
    have hcongr :
        (∫ v in (0 : ℝ)..5,
          roughSaiasDickmanDerivative (u - v) *
            roughSaiasFractionalWeight y v) =
          ∫ _v in (0 : ℝ)..5, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hv' : v ∈ Icc (0 : ℝ) 5 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] using hv
      by_cases huv : u - v < 1
      · simp [roughSaiasDickmanDerivative_of_lt_one huv]
      · have huEq : u = 1 := by linarith [hv'.1]
        have hvEq : v = 0 := by linarith [hv'.1]
        subst u
        subst v
        simp [roughSaiasFractionalWeight]
    simpa using hcongr
  rw [roughSaiasG, hzero, sub_zero, rho_eq_one_of_le_one hu]

/-- At a natural endpoint the fractional term in the normal form vanishes. -/
theorem roughSaiasLambdaNormalForm_nat
    (X y : ℕ) :
    roughSaiasLambdaNormalForm (X : ℝ) y =
      (X : ℝ) * roughSaiasG y (FriableAsymptotic.dickmanU X y) := by
  simp [roughSaiasLambdaNormalForm, FriableAsymptotic.dickmanU,
    Int.fract_natCast]



/-- For a positive natural endpoint below `y`, the finite normal form and
the genuine friable count both equal the endpoint exactly. -/
theorem roughSaiasLambdaNormalForm_eq_friableCount_initial
    {X y : ℕ} (hX : 0 < X) (hy : 1 < y) (hXy : X ≤ y) :
    roughSaiasLambdaNormalForm (X : ℝ) y =
      (FriableAsymptotic.friableCount X y : ℝ) := by
  rw [roughSaiasLambdaNormalForm_nat,
    roughSaiasG_eq_one_of_le_one
      (FriableAsymptotic.dickmanU_le_one hX hy hXy),
    mul_one, FriableAsymptotic.friableCount_eq_self hXy]

/-! ## The bounded-variation datum and compact Lipschitz reduction -/













/-- The pure real-analysis translation principle used in the paper's proof.
It is deliberately independent of `Psi`, primes, residuals, and selectors.
Mathlib currently contains bounded variation but not this standard truncated
`L¹` translation inequality in a directly applicable form. -/
def RoughCompactBVTranslationPrinciple : Prop :=
  ∀ (f : ℝ → ℝ),
    eVariationOn f (Icc (-5 : ℝ) 5) ≤ ENNReal.ofReal 2 →
    ∀ {a b : ℝ}, a ∈ Icc (0 : ℝ) 5 → b ∈ Icc (0 : ℝ) 5 →
      (∫ v in (0 : ℝ)..5, |f (a - v) - f (b - v)|) ≤
        2 * |a - b|







/-! ## The explicit `1 / log y` normalization correction -/











/-! ## Exact connection to the genuine friable residual -/

/-- The Saias normal-form main term at a natural endpoint. -/
noncomputable def roughSaiasNaturalMain (X y : ℕ) : ℝ :=
  (X : ℝ) * roughSaiasG y (FriableAsymptotic.dickmanU X y)

/-- The actual finite endpoint error `Psi - Lambda_normalForm`.  This is a
definition of a genuine number, not an assumed error function. -/
noncomputable def roughSaiasEndpointError (X y : ℕ) : ℝ :=
  (FriableAsymptotic.friableCount X y : ℝ) -
    roughSaiasNaturalMain X y

/-- The deterministic correction from the Saias normal form back to the
plain Dickman main term. -/
noncomputable def roughSaiasDickmanCorrection (X y : ℕ) : ℝ :=
  (X : ℝ) *
    (roughSaiasG y (FriableAsymptotic.dickmanU X y) -
      rho (FriableAsymptotic.dickmanU X y))

theorem roughSaiasNaturalMain_eq_lambdaNormalForm (X y : ℕ) :
    roughSaiasNaturalMain X y =
      roughSaiasLambdaNormalForm (X : ℝ) y := by
  rw [roughSaiasLambdaNormalForm_nat]
  rfl

@[simp]
theorem roughSaiasEndpointError_initial
    {X y : ℕ} (hX : 0 < X) (hy : 1 < y) (hXy : X ≤ y) :
    roughSaiasEndpointError X y = 0 := by
  unfold roughSaiasEndpointError
  rw [roughSaiasNaturalMain_eq_lambdaNormalForm,
    roughSaiasLambdaNormalForm_eq_friableCount_initial hX hy hXy]
  ring









/-- Finite endpoint-error envelope having exactly the shape obtained from
the published Hildebrand--Tenenbaum--Saias theorem on `u <= 5`.  This is a
named proposition, not a new axiom; the cited theorem must ultimately be
proved before this proposition can be instantiated in a closed proof. -/
def RoughSaiasEndpointApproximationUpToFive
    (eta : ℕ → ℝ) (Y₀ : ℕ) : Prop :=
  ∀ {X y : ℕ}, Y₀ ≤ y → 2 ≤ y → 0 < X →
    Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
    |roughSaiasEndpointError X y| ≤ eta y * (X : ℝ)



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasWeightedTransition -/
section


/-!
# Paper-scale weighted Saias transitions

The local residual predicate used by the method-of-steps development asks
for a short-interval estimate at every pair of natural endpoints.  That is
stronger than the Hildebrand--Tenenbaum--Saias input used in the paper.
The paper only needs one fixed four-endpoint block.  In that block the two
short increments have coefficients `1` and `delta * alpha`, while the broad
half-scale increment already has the coefficient `delta * beta / L`.

This file records that weaker and directly usable interface.  The endpoint
HT--Saias envelope contributes

`eta(y) * (A + B) + 5 * (B - A) / log y`

to a specified pair.  We retain those three contributions with their exact
block coefficients and close them to the existing
`roughPhysicalFriableCombination`.  No universal adjacent-pair regularity,
prime-transition predicate, selector conclusion, or new axiom is assumed.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-! ## A transition budget for one specified pair -/

/-- The exact two-endpoint ledger obtained from an HT--Saias endpoint
envelope and the deterministic normal-form correction. -/
def roughSaiasPairTransitionBudget
    (eta : ℕ → ℝ) (A B y : ℕ) : ℝ :=
  eta y * ((A : ℝ) + (B : ℝ)) +
    5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ)



/-! ## The literal weighted four-endpoint block -/

/-- The three residual transitions occurring in the paper's expanded
four-endpoint block.  The last summand is deliberately displayed with the
coefficient `|delta * (beta / L)|`: this is the broad half-scale pair, and
its paper-scale absorption uses that pre-existing `1/L`. -/
def roughPhysicalSaiasTransitionBudget
    (eta : ℕ → ℝ) (δ α β L : ℝ)
    (Xplus X Xminus Xhalf y : ℕ) : ℝ :=
  roughSaiasPairTransitionBudget eta X Xplus y +
    |δ * α| * roughSaiasPairTransitionBudget eta Xminus X y +
    |δ * (β / L)| *
      roughSaiasPairTransitionBudget eta Xhalf Xminus y

/-- The already-proved Dickman main-term and integer-endpoint imbalance
ledger, named so that the final paper-scale absorption statement is short
and can be consumed without unfolding the four coordinates. -/
def roughPhysicalDickmanTransitionLedger
    (δ α β L : ℝ) (Xplus X Xminus Xhalf y : ℕ) : ℝ :=
  (∑ i : Fin 4,
    |roughPhysicalBlockCoefficient δ α β L i| *
      (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) *
        |FriableAsymptotic.dickmanU
              (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y -
          FriableAsymptotic.dickmanU X y|) +
  |∑ i : Fin 4,
    roughPhysicalBlockCoefficient δ α β L i *
      (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ)|





/-! ## Paper-scale absorption and selector-facing closure -/





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

/-- The literal complementary factor after removing the complete rough
label. -/
def completeSmoothPart (y a : ℕ) : ℕ :=
  a / completeRoughLabel y a

/-! ## Positivity, divisibility, and product recovery -/















/-! ## The complementary low-prime factorization -/















/-! ## Uniqueness and the smooth-label criterion -/







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











@[simp]
theorem canonicalCompleteRoughRow_val
    (y : ℕ) (A : Finset ℕ) (a : CompleteRoughCandidate A) :
    (canonicalCompleteRoughRow y A a).1 =
      completeRoughLabel y a.1 := rfl

@[simp]
theorem canonicalCompleteRoughRowSignature_apply
    (y : ℕ) (A : Finset ℕ)
    (row : CanonicalCompleteRoughRow y A) :
    canonicalCompleteRoughRowSignature y A row =
      row.1.factorization := rfl

@[simp]
theorem canonicalCompleteRoughCandidateValue_apply
    (A : Finset ℕ) (a : CompleteRoughCandidate A) :
    canonicalCompleteRoughCandidateValue A a = a.1 := rfl



/-! ## Signature and value interfaces -/











/-! ## Literal subtype fibers and `rowSet` -/

/-- The complete rough row fiber expressed inside the candidate subtype. -/
def completeRoughSubtypeRowFiber
    (y : ℕ) (A : Finset ℕ) (label : ℕ) :
    Finset (CompleteRoughCandidate A) := by
  classical
  exact Finset.univ.filter
    (fun a ↦ completeRoughLabel y a.1 = label)

@[simp]
theorem mem_completeRoughSubtypeRowFiber
    {y label : ℕ} {A : Finset ℕ}
    {a : CompleteRoughCandidate A} :
    a ∈ completeRoughSubtypeRowFiber y A label ↔
      completeRoughLabel y a.1 = label := by
  classical
  simp [completeRoughSubtypeRowFiber]







/-! ## Summation and integrality bridges -/











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasCanonicalRowBridge -/
section


/-!
# Canonical-row consumer for the weighted Saias block

The analytic four-endpoint expression is useful to the construction only
after it is tied back to the literal complete-rough row used by floating
rounding.  This file supplies that consumer-facing bridge.  The sum over a
canonical `rowSet` is identified unconditionally with the already-defined
literal raw row mass.  The upper quota minus that mass is then connected to
`roughPhysicalFriableCombination` and hence to the weighted Saias bound.

The upper endpoint identification is an exact equality.  Finite head
inclusion--exclusion and the fixed-head physical shift occur between the
literal raw mass and the density-scaled four-endpoint block in the paper,
so their error is retained as a separate explicit allowance.  It is not
silently folded into the HT--Saias hypothesis.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-- The literal upper-row quota attached to a complete rough label. -/
def roughUpperCompleteRoughRowTarget
    (n h y label : ℕ) : ℕ :=
  (completeRoughRowFiber y (roughUpperBlock n h) label).card

/-- The unrestricted two-piece lower smooth mass at the three physical
endpoints. -/
def roughPhysicalLowerFriableMass
    (α β L : ℝ) (X Xminus Xhalf y : ℕ) : ℝ :=
  α * ((FriableAsymptotic.friableCount X y : ℝ) -
      (FriableAsymptotic.friableCount Xminus y : ℝ)) +
    (β / L) * ((FriableAsymptotic.friableCount Xminus y : ℝ) -
      (FriableAsymptotic.friableCount Xhalf y : ℝ))

/-- Intrinsic characterization needed to reindex one complete-rough row:
the label is positive and every factorization coordinate in its support is
strictly above the smooth cutoff. -/
def IsCompleteRoughLabel (y label : ℕ) : Prop :=
  0 < label ∧ ∀ p, label.factorization p ≠ 0 → y < p





















/-- Named finite ledger for the fixed-head shift on one canonical row. -/
def roughCanonicalFixedHeadShiftLedger
    (W n h K y : ℕ) (α β L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) : ℝ :=
  ∑ d ∈ (roughHeadModulus W).divisors,
    |(ArithmeticFunction.moebius d : ℝ)| *
      |roughSmoothPhysicalBlock
          ((n / row.1) / d)
          (((2 * n - K * h) / row.1) / d)
          (((2 * n) / row.1) / d) y α (β / L) -
        roughSmoothPhysicalBlock
          (n / row.1) ((2 * n - K * h) / row.1)
            ((2 * n) / row.1) y α (β / L) / (d : ℝ)|





/-- The quota error on the literal canonical complete-rough row. -/
def roughCanonicalRawRowQuotaError
    (W n h K y : ℕ) (α β L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) : ℝ :=
  (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) -
    ∑ a ∈ rowSet
        (canonicalCompleteRoughRow y (roughRawCandidateSet n h K)) row,
      roughHeadCompatibleRawWeight W n h K α β L
        (canonicalCompleteRoughCandidateValue
          (roughRawCandidateSet n h K) a)















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRoughRowCorrection -/
section


/-!
# Finite constant-pool correction of one canonical rough row

The Saias-facing quantity `roughCanonicalRawRowQuotaError` is a row-mass
error.  The paper corrects such an error by spreading it uniformly over a
nonempty clean broad subpool in the same complete-signature row.  This file
formalizes that finite operation directly.

No selector handoff, feasibility conclusion, prime-residual estimate, or
asymptotic pool lower bound is assumed.  Exact row mass is an algebraic
consequence of nonemptiness and containment of the correction pool.
Feasibility is then *derived* from two explicit numerical facts: the raw
coordinates have a stated two-sided margin and the constant correction
density is no larger than that margin.

The final specialization uses the literal upper-row cardinality as target,
the literal head-compatible raw weight as baseline, and the head-free broad
fiber as correction pool.  Establishing the paper's uniform lower bound for
that pool after all guards, and the corresponding `o(1 / log n)` density
bound, remains a separate arithmetic task.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Generic finite constant-pool correction -/

/-- The signed amount added to every member of a correction pool. -/
def bankPaperConstantPoolCorrectionDensity
    (row pool : Finset ℕ) (x : ℕ → ℝ) (target : ℝ) : ℝ :=
  (target - ∑ a ∈ row, x a) / (pool.card : ℝ)

/-- Add the same correction density on `pool` and leave every other
coordinate unchanged. -/
def bankPaperConstantPoolCorrection
    (row pool : Finset ℕ) (x : ℕ → ℝ) (target : ℝ)
    (a : ℕ) : ℝ :=
  x a + if a ∈ pool then
    bankPaperConstantPoolCorrectionDensity row pool x target
  else 0

@[simp]
theorem bankPaperConstantPoolCorrection_apply_of_mem
    {row pool : Finset ℕ} {x : ℕ → ℝ} {target : ℝ} {a : ℕ}
    (ha : a ∈ pool) :
    bankPaperConstantPoolCorrection row pool x target a =
      x a + bankPaperConstantPoolCorrectionDensity row pool x target := by
  simp [bankPaperConstantPoolCorrection, ha]

@[simp]
theorem bankPaperConstantPoolCorrection_apply_of_not_mem
    {row pool : Finset ℕ} {x : ℕ → ℝ} {target : ℝ} {a : ℕ}
    (ha : a ∉ pool) :
    bankPaperConstantPoolCorrection row pool x target a = x a := by
  simp [bankPaperConstantPoolCorrection, ha]







/-! ## Literal canonical rough-row specialization -/

/-- Before numerical guards, the paper's broad correction pool in one
complete rough row consists of the head-free broad candidates in that row. -/
def roughCanonicalBroadCorrectionPool
    (W n h K y label : ℕ) : Finset ℕ :=
  completeRoughRowFiber y
    (roughHeadFree W (roughBroadLowerBlock n h K)) label

/-- The broad correction pool is contained in the corresponding literal
raw-candidate row. -/
theorem roughCanonicalBroadCorrectionPool_subset_rawRow
    (W n h K y label : ℕ) :
    roughCanonicalBroadCorrectionPool W n h K y label ⊆
      completeRoughRowFiber y (roughRawCandidateSet n h K) label := by
  intro a ha
  have haData := mem_completeRoughRowFiber.mp ha
  have haHead := mem_roughHeadFree.mp haData.1
  apply mem_completeRoughRowFiber.mpr
  refine ⟨?_, haData.2⟩
  simp only [roughRawCandidateSet]
  exact Finset.mem_union_right _ haHead.1

/-- Every coordinate of the literal broad correction pool has exactly the
broad raw weight `beta / L`. -/
theorem roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
    {W n h K y label a : ℕ} {alpha beta L : ℝ}
    (ha : a ∈ roughCanonicalBroadCorrectionPool W n h K y label) :
    roughHeadCompatibleRawWeight W n h K alpha beta L a = beta / L := by
  have haData := mem_completeRoughRowFiber.mp ha
  have haHead := mem_roughHeadFree.mp haData.1
  have haHigh : a ∉ roughHighLowerBlock n h K := by
    intro haHigh
    exact Finset.disjoint_left.mp
      (roughHighLowerBlock_disjoint_roughBroadLowerBlock n h K)
      haHigh haHead.1
  simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
    haHead.2, haHigh, haHead.1]











/-! ## Assembly over all attained complete rough rows -/













/-! ## Unconditional capped-quota selector -/

/-- The largest part of the literal upper-row quota that can be placed in
the raw lower row without any arithmetic capacity theorem. -/
def roughCanonicalCappedUpperQuota
    (n h K y label : ℕ) : ℕ :=
  min (roughUpperCompleteRoughRowTarget n h y label)
    (completeRoughRowFiber y
      (roughRawCandidateSet n h K) label).card

/-- An unconditional row-constant selector carrying the capped quota.  It
is zero off the literal raw candidate set. -/
def roughCanonicalCappedUpperQuotaSelector
    (n h K y : ℕ) (a : ℕ) : ℝ :=
  if a ∈ roughRawCandidateSet n h K then
    (roughCanonicalCappedUpperQuota n h K y
        (completeRoughLabel y a) : ℝ) /
      ((completeRoughRowFiber y (roughRawCandidateSet n h K)
        (completeRoughLabel y a)).card : ℝ)
  else 0

@[simp]
theorem roughCanonicalCappedUpperQuotaSelector_apply_of_mem
    {n h K y a : ℕ} (ha : a ∈ roughRawCandidateSet n h K) :
    roughCanonicalCappedUpperQuotaSelector n h K y a =
      (roughCanonicalCappedUpperQuota n h K y
          (completeRoughLabel y a) : ℝ) /
        ((completeRoughRowFiber y (roughRawCandidateSet n h K)
          (completeRoughLabel y a)).card : ℝ) := by
  simp [roughCanonicalCappedUpperQuotaSelector, ha]

@[simp]
theorem roughCanonicalCappedUpperQuotaSelector_apply_of_not_mem
    {n h K y a : ℕ} (ha : a ∉ roughRawCandidateSet n h K) :
    roughCanonicalCappedUpperQuotaSelector n h K y a = 0 := by
  simp [roughCanonicalCappedUpperQuotaSelector, ha]













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightLedger -/
section


/-!
# The exact smooth-row quota and height ledger from Section 8

This file records the algebraic part of the paper's smooth-row initialization
without replacing any actual finite mass by an asymptotic main term.

The literal active base component is the constant weight `betaAct / L n` on
the head-free, `yNat n`-smooth part of the broad interval.  Its exact support
is the complete-rough row with label one.  The later definitions follow the
paper verbatim:

* `Q_sm(0)` is the nearest integer to `m_sm,fr + qTilde`, with a half-integer
  tie sent to the smaller integer;
* `q0 = Q_sm(0) - m_sm,fr`;
* `Q_sm(d) = Q_sm(0) - d` and `qAct(d) = q0 - d`;
* `A0 = logY - Lambda0 - q0 * L` and `A(d) = A0 + d * L`;
* `d` is the tie-lower nearest integer to
  `(mu * q0 - A0) / (L + mu)`.

All displayed identities and the two nearest-integer errors are unconditional.
The analytic comparison between the raw base mass and the actual post-guard
mass is deliberately left to the companion asymptotic module.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal rough smooth base component -/

/-- The paper's pre-guard active smooth support: the complete-rough row of
label one inside the head-free broad interval. -/
def bankPaperCanonicalRawSmoothBasePool
    (W n h K : Nat) : Finset Nat :=
  roughCanonicalBroadCorrectionPool W n h K (yNat n) 1



/-- Exact finite mass of the active smooth base component. -/
def bankPaperCanonicalRawSmoothBaseMass
    (W n h K : Nat) (betaAct : Real) : Real :=
  betaAct / L n *
    ((bankPaperCanonicalRawSmoothBasePool W n h K).card : Real)











/-! ## Tie-lower nearest integers -/

/-- Nearest-integer rounding with the paper's convention: an exact
half-integer is sent to the smaller integer. -/
def bankPaperNearestIntegerTieLower (x : Real) : Int :=
  ⌈x - 1 / 2⌉

/-- The half-open Voronoi cell characterizing tie-lower rounding.  The closed
right endpoint is exactly the smaller-integer tie convention. -/
theorem bankPaperNearestIntegerTieLower_eq_iff
    (x : Real) (k : Int) :
    bankPaperNearestIntegerTieLower x = k ↔
      (k : Real) - 1 / 2 < x ∧ x ≤ (k : Real) + 1 / 2 := by
  unfold bankPaperNearestIntegerTieLower
  rw [Int.ceil_eq_iff]
  constructor <;> rintro ⟨hleft, hright⟩ <;>
    constructor <;> linarith

/-- Integer inputs are fixed. -/
@[simp] theorem bankPaperNearestIntegerTieLower_intCast (k : Int) :
    bankPaperNearestIntegerTieLower (k : Real) = k := by
  apply (bankPaperNearestIntegerTieLower_eq_iff (k : Real) k).2
  constructor <;> linarith

/-- At a positive half tie the smaller adjacent integer is selected. -/
@[simp] theorem bankPaperNearestIntegerTieLower_add_half (k : Int) :
    bankPaperNearestIntegerTieLower ((k : Real) + 1 / 2) = k := by
  apply (bankPaperNearestIntegerTieLower_eq_iff
    ((k : Real) + 1 / 2) k).2
  constructor <;> linarith



/-! ## Exact smooth-row quota initialization -/

/-- `Q_sm(0)`, formed from the actual frozen and post-guard active masses. -/
def bankPaperCanonicalSmoothInitialQuota
    (mFrozen qTilde : Real) : Int :=
  bankPaperNearestIntegerTieLower (mFrozen + qTilde)

/-- `q0 = Q_sm(0) - m_sm,fr`; this is a real mass, not an integer. -/
def bankPaperCanonicalSmoothInitialActiveMass
    (mFrozen qTilde : Real) : Real :=
  (bankPaperCanonicalSmoothInitialQuota mFrozen qTilde : Real) - mFrozen









/-- The real active quota `qAct(d) = q0 - d`. -/
def bankPaperCanonicalSmoothActiveMassAt
    (mFrozen qTilde : Real) (d : Int) : Real :=
  bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - (d : Real)













/-! ## Exact frozen-height ledger and centered adjustment -/

/-- `A0 = logY - Lambda0 - q0 * L`. -/
def bankPaperCanonicalSmoothFrozenHeightDefect
    (n : Nat) (logY Lambda0 q0 : Real) : Real :=
  logY - Lambda0 - q0 * L n

/-- The active height after an arbitrary integer change `d`. -/
def bankPaperCanonicalSmoothActiveHeightAt
    (n : Nat) (logY Lambda0 q0 : Real) (d : Int) : Real :=
  logY - Lambda0 - (q0 - (d : Real)) * L n



/-- The real height center `dStar = (mu q0 - A0) / (L + mu)`. -/
def bankPaperCanonicalSmoothHeightCenter
    (n : Nat) (mu q0 A0 : Real) : Real :=
  (mu * q0 - A0) / (L n + mu)

/-- The paper's integer height adjustment, with the same tie-lower rule as
the initial quota. -/
def bankPaperCanonicalSmoothHeightAdjustment
    (n : Nat) (mu q0 A0 : Real) : Int :=
  bankPaperNearestIntegerTieLower
    (bankPaperCanonicalSmoothHeightCenter n mu q0 A0)

















/-! ## Literal Section 8 families -/

/-- The paper's varying initial active mass `q0(n)`, built from the actual
frozen and post-guard mass families. -/
def bankPaperCanonicalSmoothQ0Family
    (mFrozen qTilde : Nat -> Real) (n : Nat) : Real :=
  bankPaperCanonicalSmoothInitialActiveMass (mFrozen n) (qTilde n)

/-- The varying frozen height defect formed from the literal `q0` family. -/
def bankPaperCanonicalSmoothA0Family
    (logY Lambda0 mFrozen qTilde : Nat -> Real) (n : Nat) : Real :=
  bankPaperCanonicalSmoothFrozenHeightDefect n (logY n) (Lambda0 n)
    (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)



/-- The literal integer height-adjustment family `d(n)`. -/
def bankPaperCanonicalSmoothDIntFamily
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (n : Nat) : Int :=
  bankPaperCanonicalSmoothHeightAdjustment n mu
    (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
    (bankPaperCanonicalSmoothA0Family logY Lambda0 mFrozen qTilde n)

/-- The same integer adjustment viewed as a real function for asymptotic
notation. -/
def bankPaperCanonicalSmoothDRealFamily
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (n : Nat) : Real :=
  (bankPaperCanonicalSmoothDIntFamily mu logY Lambda0 mFrozen qTilde n : Real)

/-- The final Section 8 active-mass family `qAct(d)`. -/
def bankPaperCanonicalSmoothFinalActiveMassFamily
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (n : Nat) : Real :=
  bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
    bankPaperCanonicalSmoothDRealFamily mu logY Lambda0 mFrozen qTilde n

/-- The literal remaining active height after applying the integer family
`d(n)`. -/
def bankPaperCanonicalSmoothFinalActiveHeightFamily
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (n : Nat) : Real :=
  bankPaperCanonicalSmoothActiveHeightAt n (logY n) (Lambda0 n)
    (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
    (bankPaperCanonicalSmoothDIntFamily
      mu logY Lambda0 mFrozen qTilde n)

/-- The centered physical-mean error from the paper's display. -/
def bankPaperCanonicalSmoothPhysicalMeanErrorFamily
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (n : Nat) : Real :=
  bankPaperCanonicalSmoothFinalActiveHeightFamily
      mu logY Lambda0 mFrozen qTilde n /
    bankPaperCanonicalSmoothFinalActiveMassFamily
      mu logY Lambda0 mFrozen qTilde n - mu









end

end Erdos390.WholePaper

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

/-- Multiplicity of a marker in a finite marker--donor eligibility relation. -/
def bankDonorMultiplicity {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) (marker : Marker) : ℕ :=
  (eligible.filter fun pair ↦ pair.1 = marker).card



/-- Total number of eligible marker--donor occurrences. -/
def bankMarkerOccurrenceTotal {Marker Donor : Type*}
    (eligible : Finset (Marker × Donor)) : ℕ :=
  eligible.card

/-- Number of markers having at least one eligible donor. -/
def bankEligibleMarkerCount {Marker Donor : Type*} [DecidableEq Marker]
    (eligible : Finset (Marker × Donor)) : ℕ :=
  (bankEligibleMarkers eligible).card













theorem bankChosenMarkerDonor_mem
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor))
    (marker : ↑(bankEligibleMarkers eligible)) :
    bankChosenMarkerDonor eligible marker ∈ eligible := by
  exact Classical.choose_spec
    (eligibleMarker_exists_donor eligible marker.property)





theorem bankMarkerDonorPairs_subset_eligible
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    bankMarkerDonorPairs eligible ⊆ eligible := by
  rw [bankMarkerDonorPairs, Finset.image_subset_iff]
  intro marker _hmarker
  exact bankChosenMarkerDonor_mem eligible marker





/-- No two selected pairs with the same marker can differ in their donor. -/
theorem bankMarkerDonorPairs_injective_by_marker
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor))
    {pair pair' : Marker × Donor}
    (hpair : pair ∈ bankMarkerDonorPairs eligible)
    (hpair' : pair' ∈ bankMarkerDonorPairs eligible)
    (hmarker : pair.1 = pair'.1) :
    pair = pair' := by
  unfold bankMarkerDonorPairs at hpair hpair'
  rcases Finset.mem_image.mp hpair with ⟨marker, _hmarkerMem, rfl⟩
  rcases Finset.mem_image.mp hpair' with ⟨marker', _hmarkerMem', rfl⟩
  have hmarkers : marker = marker' := by
    apply Subtype.ext
    exact hmarker
  subst marker'
  rfl







theorem bankOrientationPoolFirst_subset_pairs
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    bankOrientationPoolFirst eligible ⊆ bankMarkerDonorPairs eligible := by
  exact (Classical.choose_spec
    (half_card_subset_exists (bankMarkerDonorPairs eligible))).1



theorem bankOrientationPools_disjoint
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    Disjoint (bankOrientationPoolFirst eligible)
      (bankOrientationPoolSecond eligible) := by
  rw [Finset.disjoint_left]
  intro pair hfirst hsecond
  exact (Finset.mem_sdiff.mp hsecond).2 hfirst







theorem bankOrientationPoolFirst_subset_eligible
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    bankOrientationPoolFirst eligible ⊆ eligible :=
  (bankOrientationPoolFirst_subset_pairs eligible).trans
    (bankMarkerDonorPairs_subset_eligible eligible)

theorem bankOrientationPoolSecond_subset_eligible
    {Marker Donor : Type*} [DecidableEq Marker] [DecidableEq Donor]
    (eligible : Finset (Marker × Donor)) :
    bankOrientationPoolSecond eligible ⊆ eligible := by
  intro pair hpair
  exact bankMarkerDonorPairs_subset_eligible eligible
    (Finset.mem_sdiff.mp hpair).1



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







/-- Actual requests routed to one bottom orientation pool. -/
def bankBottomRequestsInPool
    {Request : Type*} [DecidableEq Request]
    (requests : Finset Request)
    (poolOf : Request → BankBottomOrientationPool)
    (pool : BankBottomOrientationPool) : Finset Request :=
  requests.filter fun request ↦ poolOf request = pool

/-- Literal demand of one bottom orientation pool. -/
def bankBottomPoolDemand
    {Request : Type*} [DecidableEq Request]
    (requests : Finset Request)
    (poolOf : Request → BankBottomOrientationPool)
    (pool : BankBottomOrientationPool) : ℕ :=
  (bankBottomRequestsInPool requests poolOf pool).card

/-- Literal number of available occurrences in one bottom orientation pool. -/
def bankBottomPoolCapacity
    {Occurrence : Type*}
    (available : BankBottomOrientationPool → Finset Occurrence)
    (pool : BankBottomOrientationPool) : ℕ :=
  (available pool).card

/-- An assignment consists of an embedding from each request fiber into its
actual finite occurrence pool.  Membership and within-pool injectivity are
carried by the subtype embedding itself. -/
structure BankBottomPoolMatching
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    (requests : Finset Request)
    (poolOf : Request → BankBottomOrientationPool)
    (available : BankBottomOrientationPool → Finset Occurrence) where
  toEmbedding : (pool : BankBottomOrientationPool) →
    ↑(bankBottomRequestsInPool requests poolOf pool) ↪
      ↑(available pool)



/-- Regard an original request as a member of the fiber bearing its label. -/
def bankBottomRequestInItsPool
    {Request : Type*} [DecidableEq Request]
    {requests : Finset Request}
    (poolOf : Request → BankBottomOrientationPool)
    (request : ↑requests) :
    ↑(bankBottomRequestsInPool requests poolOf (poolOf request.1)) :=
  ⟨request.1, Finset.mem_filter.mpr ⟨request.property, rfl⟩⟩

/-- The sigma type that keeps the pool label attached to a request fiber. -/
abbrev BankBottomLabeledRequest
    {Request : Type*} [DecidableEq Request]
    (requests : Finset Request)
    (poolOf : Request → BankBottomOrientationPool) :=
  Σ pool : BankBottomOrientationPool,
    ↑(bankBottomRequestsInPool requests poolOf pool)

/-- Attach the prescribed pool label to an original request. -/
def bankBottomLabelRequest
    {Request : Type*} [DecidableEq Request]
    {requests : Finset Request}
    (poolOf : Request → BankBottomOrientationPool)
    (request : ↑requests) :
    BankBottomLabeledRequest requests poolOf :=
  ⟨poolOf request.1, bankBottomRequestInItsPool poolOf request⟩



/-- Evaluate the poolwise matching while retaining the pool label. -/
def BankBottomPoolMatching.slotOfLabeledRequest
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (request : BankBottomLabeledRequest requests poolOf) : Occurrence :=
  (matching.toEmbedding request.1 request.2).1

theorem BankBottomPoolMatching.slotOfLabeledRequest_mem
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (request : BankBottomLabeledRequest requests poolOf) :
    matching.slotOfLabeledRequest request ∈ available request.1 :=
  (matching.toEmbedding request.1 request.2).property



/-- The actual occurrence assigned to an original request. -/
def BankBottomPoolMatching.matchedSlot
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (request : ↑requests) : Occurrence :=
  matching.slotOfLabeledRequest (bankBottomLabelRequest poolOf request)

theorem BankBottomPoolMatching.matchedSlot_mem
    {Request Occurrence : Type*}
    [DecidableEq Request] [DecidableEq Occurrence]
    {requests : Finset Request}
    {poolOf : Request → BankBottomOrientationPool}
    {available : BankBottomOrientationPool → Finset Occurrence}
    (matching : BankBottomPoolMatching requests poolOf available)
    (request : ↑requests) :
    matching.matchedSlot request ∈ available (poolOf request.1) :=
  matching.slotOfLabeledRequest_mem (bankBottomLabelRequest poolOf request)













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





























theorem bankBottomMarkerLower_le_upper
    {n M : ℕ} (hM : 2 * n ≤ M) (move : BankBottomMove) :
    bankBottomMarkerLower n move ≤ bankBottomMarkerUpper M move := by
  cases move <;>
    simp only [bankBottomMarkerLower, bankBottomMarkerUpper] <;> omega

theorem bankBottomMarkerLower_le_cut
    (n M : ℕ) (move : BankBottomMove) :
    bankBottomMarkerLower n move ≤ bankBottomOrientationCut n M move := by
  simp only [bankBottomOrientationCut, Nat.le_add_right]

theorem bankBottomOrientationCut_le_upper
    {n M : ℕ} (hM : 2 * n ≤ M) (move : BankBottomMove) :
    bankBottomOrientationCut n M move ≤ bankBottomMarkerUpper M move := by
  have hlower := bankBottomMarkerLower_le_upper hM move
  unfold bankBottomOrientationCut
  omega





theorem bankBottomOrientedMarkerInterval_subset
    {n M : ℕ} (hM : 2 * n ≤ M)
    (pool : BankBottomOrientationPool) :
    bankBottomOrientedMarkerInterval n M pool ⊆
      bankBottomMarkerInterval n M pool.1 := by
  rcases pool with ⟨move, orientation⟩
  cases orientation
  · intro marker hmarker
    have hcut := bankBottomOrientationCut_le_upper hM move
    simp only [bankBottomOrientedMarkerInterval, bankBottomMarkerInterval,
      Finset.mem_Ioc] at hmarker ⊢
    exact ⟨hmarker.1, hmarker.2.trans hcut⟩
  · intro marker hmarker
    have hlower := bankBottomMarkerLower_le_cut n M move
    simp only [bankBottomOrientedMarkerInterval, bankBottomMarkerInterval,
      Finset.mem_Ioc] at hmarker ⊢
    exact ⟨lt_of_le_of_lt hlower hmarker.1, hmarker.2⟩





/-- In the `3→2` row the donor is literally the upper-state occurrence. -/
@[simp] theorem bankBottomDonor_threeToTwo_eq_upperState (marker : ℕ) :
    bankBottomDonor .threeToTwo marker =
      bankBottomUpperState .threeToTwo marker := rfl

/-- In the terminal `2→1` row the donor is literally the upper-state
occurrence. -/
@[simp] theorem bankBottomDonor_twoToOne_eq_upperState (marker : ℕ) :
    bankBottomDonor .twoToOne marker =
      bankBottomUpperState .twoToOne marker := rfl

@[simp] theorem bankBottomComponentOccurrences_threeToTwo (marker : ℕ) :
    bankBottomComponentOccurrences .threeToTwo marker =
      {2 * marker, 3 * marker} := by
  ext occurrence
  simp [bankBottomComponentOccurrences, bankBottomLowerState,
    bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier]

@[simp] theorem bankBottomComponentOccurrences_twoToOne (marker : ℕ) :
    bankBottomComponentOccurrences .twoToOne marker =
      {2 * marker, 4 * marker} := by
  ext occurrence
  simp [bankBottomComponentOccurrences, bankBottomLowerState,
    bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier]











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.SafeShortIntervalPrimeCounting -/
section


/-!
# Safe prime counting in moving short intervals

This module extracts the short-interval consequence that is actually needed
for the bottom marker banks.  The proof does **not** subtract two copies of
the public `O(x / log(x)^2)` remainder for `pi`.  Such a subtraction would
leave an error on the same scale as the desired answer.

Instead, it subtracts the stronger audited estimates
`theta(x) - x = O(x / log(x)^2)`.  At asymptotically linear endpoints this
error is `o(n / log n)`.  The logarithmic weights on a prime interval are
then squeezed between the logarithms of its two endpoints.  Dividing those
weights out supplies the additional logarithm and gives an unweighted prime
count on the scale `n / (log n)^2`.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper.SafePrimeCounting

noncomputable section

/-- The unweighted prime scale for intervals of length `n / log n`. -/
def shortIntervalPrimeScale (n : ℕ) : ℝ :=
  Erdos390.WholePaper.secondOrderScale n / Real.log (n : ℝ)





















end

end Erdos390.WholePaper.SafePrimeCounting

end

/- Source module: Erdos390.WholePaper.BankBottomMarkerPoolScale -/
section


/-!
# Prime-counting scales for bottom marker pools

The bottom intervals have length of order `n / log n`, while their prime
cardinality has order `n / log n ^ 2`.  Consequently their cardinality
divided by `secondOrderScale n = n / log n` tends to zero, not to a positive
constant.  This file records that coarse-scale fact and then applies the
audited `theta`-difference squeeze to obtain the positive constants on the
finer scale `secondOrderScale n / log n`.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

/-- The scale `N/L = n/(log n)^2` used by the paper for bottom primes. -/
def bankBottomPrimeScale (n : ℕ) : ℝ :=
  SafePrimeCounting.shortIntervalPrimeScale n









/-- Common first-order location of the two endpoints of a bottom row. -/
def bankBottomMarkerBase : BankBottomMove → ℝ
  | .fiveToFour => 1 / 3
  | .fourToThree => 2 / 5
  | .threeToTwo => 2 / 3
  | .twoToOne => 1 / 2







/-- The divisor through which the upper-tail length enters each bottom row. -/
def bankBottomMarkerDenominator : BankBottomMove → ℕ
  | .fiveToFour => 6
  | .fourToThree => 5
  | .threeToTwo => 3
  | .twoToOne => 4



/-- Lower endpoint of an oriented half-pool. -/
def bankBottomOrientedMarkerLower (n M : ℕ)
    (pool : BankBottomOrientationPool) : ℕ :=
  match pool.2 with
  | .downward => bankBottomMarkerLower n pool.1
  | .upward => bankBottomOrientationCut n M pool.1

/-- Upper endpoint of an oriented half-pool. -/
def bankBottomOrientedMarkerUpper (n M : ℕ)
    (pool : BankBottomOrientationPool) : ℕ :=
  match pool.2 with
  | .downward => bankBottomOrientationCut n M pool.1
  | .upward => bankBottomMarkerUpper M pool.1

@[simp] theorem bankBottomOrientedMarkerInterval_eq_Ioc
    (n M : ℕ) (pool : BankBottomOrientationPool) :
    bankBottomOrientedMarkerInterval n M pool =
      Finset.Ioc (bankBottomOrientedMarkerLower n M pool)
        (bankBottomOrientedMarkerUpper n M pool) := by
  rcases pool with ⟨move, orientation⟩
  cases orientation <;>
    rfl

















/-- Limiting supply constant for either orientation of a bottom row. -/
def bankBottomOrientedPrimeConstant
    (c : ℝ) (pool : BankBottomOrientationPool) : ℝ :=
  c / (2 * (bankBottomMarkerDenominator pool.1 : ℝ))

















end

end Erdos390.WholePaper

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







/-- A prime has its coordinate unit valuation vector. -/
theorem integerValuationVector_prime {p : ℕ} (hp : p.Prime) :
    integerValuationVector p = coordinateUnit p := by
  funext q
  rw [integerValuationVector, hp.factorization]
  by_cases hpq : p = q
  · subst q
    simp [coordinateUnit]
  · simp [coordinateUnit, hpq]

/-- A prime power has the expected integer valuation vector. -/
theorem integerValuationVector_prime_pow {p k : ℕ} (hp : p.Prime) :
    integerValuationVector (p ^ k) =
      (k : ℤ) • coordinateUnit p := by
  funext q
  rw [integerValuationVector, hp.factorization_pow]
  by_cases hpq : p = q
  · subst q
    simp [coordinateUnit]
  · simp [coordinateUnit, hpq]



















/-- Each displayed bottom vector is the valuation change of its literal
integer-core move. -/
theorem factorMoveChange_five_to_four :
    factorMoveChange 5 4 = bottomFiveToFourChange := by
  have htwo : Nat.Prime 2 := by norm_num
  have hfive : Nat.Prime 5 := by norm_num
  rw [factorMoveChange, show 4 = 2 ^ 2 by norm_num,
    integerValuationVector_prime_pow htwo,
    integerValuationVector_prime hfive]
  rfl

theorem factorMoveChange_four_to_three :
    factorMoveChange 4 3 = bottomFourToThreeChange := by
  have htwo : Nat.Prime 2 := by norm_num
  have hthree : Nat.Prime 3 := by norm_num
  rw [factorMoveChange, show 4 = 2 ^ 2 by norm_num,
    integerValuationVector_prime_pow htwo,
    integerValuationVector_prime hthree]
  rfl

theorem factorMoveChange_three_to_two :
    factorMoveChange 3 2 = bottomThreeToTwoChange := by
  have htwo : Nat.Prime 2 := by norm_num
  have hthree : Nat.Prime 3 := by norm_num
  rw [factorMoveChange, integerValuationVector_prime htwo,
    integerValuationVector_prime hthree]
  rfl













/-- The short bottom paths for the exceptional source primes. -/
theorem three_to_one_change_eq_neg_unit_three :
    bottomThreeToTwoChange + bottomTwoToOneChange =
      -coordinateUnit 3 := by
  rw [bottomThreeToTwoChange, bottomTwoToOneChange]
  abel

theorem two_to_one_change_eq_neg_unit_two :
    bottomTwoToOneChange = -coordinateUnit 2 := rfl











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













theorem bankRoundingPrimeSupport_prime
    {n p : ℕ} (hp : p ∈ bankRoundingPrimeSupport n) : p.Prime := by
  exact Nat.prime_of_mem_primesBelow hp

theorem bankRoundingPrimeSupport_le_yNat
    {n p : ℕ} (hp : p ∈ bankRoundingPrimeSupport n) : p ≤ yNat n := by
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mem_primesBelow hp)











/-- Total demand in each fixed move/orientation fiber. -/
def bankBottomPaperDemand (n : ℕ) : ℕ :=
  ∑ p ∈ bankRoundingPrimeSupport n, bankRoundingBeta n p

 def bankBottomPaperRequestFiberEquiv
    (n : ℕ) (pool : BankBottomOrientationPool) :
    ↑(bankBottomRequestsInPool (bankBottomPaperRequests n)
        (bankBottomPaperRequestPool n) pool) ≃
      Σ p : ↑(bankRoundingPrimeSupport n),
        Fin (bankRoundingBetaOnSupport n p) where
  toFun request :=
    ⟨request.1.1.1, match request.1.1.2 with
      | .inl copy => copy
      | .inr copy => copy⟩
  invFun indexed :=
    ⟨(⟨indexed.1, match pool.2 with
        | .downward => Sum.inl indexed.2
        | .upward => Sum.inr indexed.2⟩, pool.1), by
      rcases pool with ⟨move, orientation⟩
      cases orientation <;>
      simp [bankBottomRequestsInPool, bankBottomPaperRequests,
        bankBottomPaperRequestPool, bankSignedSlotOrientation]⟩
  left_inv request := by
    rcases pool with ⟨poolMove, poolOrientation⟩
    rcases request with ⟨⟨⟨prime, signedCopy⟩, move⟩, hrequest⟩
    have hpool :
        (move, bankSignedSlotOrientation ⟨prime, signedCopy⟩) =
          (poolMove, poolOrientation) := by
      simpa only [bankBottomRequestsInPool, bankBottomPaperRequests,
        bankBottomPaperRequestPool, Finset.mem_filter, Finset.mem_univ,
        true_and] using hrequest
    cases signedCopy with
    | inl copy =>
        simp only [bankSignedSlotOrientation] at hpool
        cases hpool
        rfl
    | inr copy =>
        simp only [bankSignedSlotOrientation] at hpool
        cases hpool
        rfl
  right_inv indexed := by
    rcases pool with ⟨move, orientation⟩
    rcases indexed with ⟨prime, copy⟩
    cases orientation <;> rfl



/-- Fifth-root cutoff used only to count the small head of the beta sum. -/
def bankRoundingHeadCutoff (n : ℕ) : ℕ :=
  ⌊(3 * (n : ℝ)) ^ (1 / 5 : ℝ)⌋₊

/-- A convenient explicit natural majorant for the common pool demand. -/
def bankBottomPaperDemandMajorant (n : ℕ) : ℕ :=
  4 * bankRoundingDepth n * bankRoundingDepth n *
      (bankRoundingHeadCutoff n + 1) +
    20 * bankRoundingDepth n * Nat.primeCounting (yNat n)



































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







@[simp] theorem bankBottomIncidentStateCores_fiveToFour :
    bankBottomIncidentStateCores .fiveToFour = (4, 5) := rfl

@[simp] theorem bankBottomIncidentStateCores_fourToThree :
    bankBottomIncidentStateCores .fourToThree = (3, 4) := rfl

@[simp] theorem bankBottomIncidentStateCores_threeToTwo :
    bankBottomIncidentStateCores .threeToTwo = (2, 3) := rfl

@[simp] theorem bankBottomIncidentStateCores_twoToOne :
    bankBottomIncidentStateCores .twoToOne = (2, 4) := rfl











@[simp] theorem bankBottomRelevantMoves_three :
    bankBottomRelevantMoves 3 = {.threeToTwo, .twoToOne} := by
  ext move
  cases move <;>
    simp [bankBottomRelevantMoves, bankBottomMoveRelevantForPrime]

@[simp] theorem bankBottomRelevantMoves_two :
    bankBottomRelevantMoves 2 = {.twoToOne} := by
  ext move
  cases move <;>
    simp [bankBottomRelevantMoves, bankBottomMoveRelevantForPrime]

























/-! ## The deterministic truncated bottom path -/



@[simp] theorem bankBottomMoveChange_fiveToFour :
    bankBottomMoveChange .fiveToFour = bottomFiveToFourChange := by
  simpa [bankBottomMoveChange, bankBottomUpperStateMultiplier,
    bankBottomLowerStateMultiplier] using factorMoveChange_five_to_four

@[simp] theorem bankBottomMoveChange_fourToThree :
    bankBottomMoveChange .fourToThree = bottomFourToThreeChange := by
  simpa [bankBottomMoveChange, bankBottomUpperStateMultiplier,
    bankBottomLowerStateMultiplier] using factorMoveChange_four_to_three

@[simp] theorem bankBottomMoveChange_threeToTwo :
    bankBottomMoveChange .threeToTwo = bottomThreeToTwoChange := by
  simpa [bankBottomMoveChange, bankBottomUpperStateMultiplier,
    bankBottomLowerStateMultiplier] using factorMoveChange_three_to_two

theorem factorMoveChange_four_to_two :
    factorMoveChange 4 2 = bottomTwoToOneChange := by
  have htwo : Nat.Prime 2 := by norm_num
  rw [factorMoveChange, show 4 = 2 ^ 2 by norm_num,
    integerValuationVector_prime_pow htwo,
    integerValuationVector_prime htwo,
    bottomTwoToOneChange]
  abel

@[simp] theorem bankBottomMoveChange_twoToOne :
    bankBottomMoveChange .twoToOne = bottomTwoToOneChange := by
  simpa [bankBottomMoveChange, bankBottomUpperStateMultiplier,
    bankBottomLowerStateMultiplier] using factorMoveChange_four_to_two





@[simp] theorem bankBottomPathChange_three :
    bankBottomPathChange 3 = -coordinateUnit 3 := by
  calc
    bankBottomPathChange 3 =
        bottomThreeToTwoChange + bottomTwoToOneChange := by
      rw [bankBottomPathChange, bankBottomRelevantMoves_three]
      simp
    _ = -coordinateUnit 3 := three_to_one_change_eq_neg_unit_three

@[simp] theorem bankBottomPathChange_two :
    bankBottomPathChange 2 = -coordinateUnit 2 := by
  calc
    bankBottomPathChange 2 = bottomTwoToOneChange := by
      rw [bankBottomPathChange, bankBottomRelevantMoves_two]
      simp
    _ = -coordinateUnit 2 := two_to_one_change_eq_neg_unit_two





/-! ## A realization obtained from the actual matching -/



/-- Turn the concrete pool matching into component data. -/
def BankBottomPaperRealization.ofMatching
    {n M : ℕ}
    (matching : BankBottomPoolMatching
      (bankBottomPaperRequests n) (bankBottomPaperRequestPool n)
      (fun pool ↦ bankBottomOrientedMarkerPrimes n M pool))
    (hinjective : Function.Injective matching.matchedSlot) :
    BankBottomPaperRealization n M where
  marker := matching.matchedSlot
  marker_mem := matching.matchedSlot_mem
  marker_injective := hinjective

namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)











theorem marker_prime (request : ↑(bankBottomPaperRequests n)) :
    (realization.marker request).Prime :=
  (Finset.mem_filter.mp (realization.marker_mem request)).2

theorem marker_mem_row (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    realization.marker request ∈
      bankBottomMarkerInterval n M (realization.move request) := by
  have horiented : realization.marker request ∈
      bankBottomOrientedMarkerInterval n M
        (bankBottomPaperRequestPool n request.1) :=
    (Finset.mem_filter.mp (realization.marker_mem request)).1
  have hrow := bankBottomOrientedMarkerInterval_subset hTwoN
    (bankBottomPaperRequestPool n request.1) horiented
  simpa only [move, bankBottomPaperRequestPool] using hrow

/-- Endpoint-only marker geometry used to separate bottom markers from the
ordinary marker intervals: every bottom marker lies strictly above `n/3`. -/
theorem n_lt_three_mul_marker (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    n < 3 * realization.marker request := by
  have hrow := realization.marker_mem_row hTwoN request
  cases hmove : realization.move request <;>
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc] at hrow <;> omega













/-! The four paper rows, with the marker made explicit. -/













/-! ## Orientation-aware realized row and slot changes -/























end BankBottomPaperRealization

/-! ## Complete occurrence sets and rough signatures -/





theorem bankBottomPaperOccurrenceMultiplier_pos
    (move : BankBottomMove) (kind : BankBottomPaperOccurrenceKind) :
    0 < bankBottomPaperOccurrenceMultiplier move kind := by
  cases kind <;> cases move <;>
    norm_num [bankBottomPaperOccurrenceMultiplier,
      bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
      bankBottomDonorMultiplier]

theorem bankBottomPaperOccurrenceMultiplier_le_six
    (move : BankBottomMove) (kind : BankBottomPaperOccurrenceKind) :
    bankBottomPaperOccurrenceMultiplier move kind ≤ 6 := by
  cases kind <;> cases move <;>
    norm_num [bankBottomPaperOccurrenceMultiplier,
      bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
      bankBottomDonorMultiplier]

namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)



@[simp] theorem occurrenceValue_marker
    (request : ↑(bankBottomPaperRequests n)) :
    realization.occurrenceValue request .marker = realization.marker request := by
  simp [occurrenceValue, bankBottomPaperOccurrenceMultiplier]

@[simp] theorem occurrenceValue_lowerState
    (request : ↑(bankBottomPaperRequests n)) :
    realization.occurrenceValue request .lowerState =
      realization.lowerStateFactor request := rfl

@[simp] theorem occurrenceValue_upperState
    (request : ↑(bankBottomPaperRequests n)) :
    realization.occurrenceValue request .upperState =
      realization.upperStateFactor request := rfl

@[simp] theorem occurrenceValue_donor
    (request : ↑(bankBottomPaperRequests n)) :
    realization.occurrenceValue request .donor =
      realization.donorFactor request := rfl



theorem occurrenceValue_mem_carrierValueSet
    (request : ↑(bankBottomPaperRequests n))
    (kind : BankBottomPaperOccurrenceKind) :
    realization.occurrenceValue request kind ∈
      realization.carrierValueSet request := by
  exact Finset.mem_image.mpr ⟨kind, Finset.mem_univ kind, rfl⟩









theorem componentOccurrences_eq_states_insert_donor
    (request : ↑(bankBottomPaperRequests n)) :
    realization.componentOccurrences request =
      insert (realization.lowerStateFactor request)
        (insert (realization.upperStateFactor request)
          {realization.donorFactor request}) := rfl



theorem componentOccurrences_subset_carrierValueSet
    (request : ↑(bankBottomPaperRequests n)) :
    realization.componentOccurrences request ⊆
      realization.carrierValueSet request := by
  intro occurrence hoccurrence
  rw [componentOccurrences_eq_states_insert_donor] at hoccurrence
  simp only [Finset.mem_insert, Finset.mem_singleton] at hoccurrence
  rcases hoccurrence with hoccurrence | hoccurrence | hoccurrence
  · subst occurrence
    simpa only [occurrenceValue_lowerState] using
      realization.occurrenceValue_mem_carrierValueSet request .lowerState
  · subst occurrence
    simpa only [occurrenceValue_upperState] using
      realization.occurrenceValue_mem_carrierValueSet request .upperState
  · subst occurrence
    simpa only [occurrenceValue_donor] using
      realization.occurrenceValue_mem_carrierValueSet request .donor





















/-- Multiplication by a positive cofactor at most `y` does not change any
prime-power coordinate above `y`. -/
theorem completeRoughSignature_small_mul
    {y cofactor marker : ℕ} (hcofactorPos : 0 < cofactor)
    (hcofactorLe : cofactor ≤ y) (hmarker : marker ≠ 0) :
    completeRoughSignature y (cofactor * marker) =
      completeRoughSignature y marker := by
  ext p
  rw [completeRoughSignature_apply, completeRoughSignature_apply]
  by_cases hp : y < p
  · rw [if_pos hp, if_pos hp,
      Nat.factorization_mul hcofactorPos.ne' hmarker]
    simp only [Finsupp.add_apply,
      Nat.factorization_eq_zero_of_lt (hcofactorLe.trans_lt hp), zero_add]
  · simp only [if_neg hp]

theorem occurrenceValue_completeRoughSignature
    (hySix : 6 ≤ yNat n)
    (request : ↑(bankBottomPaperRequests n))
    (kind : BankBottomPaperOccurrenceKind) :
    completeRoughSignature (yNat n)
        (realization.occurrenceValue request kind) =
      completeRoughSignature (yNat n) (realization.marker request) := by
  apply completeRoughSignature_small_mul
  · exact bankBottomPaperOccurrenceMultiplier_pos _ _
  · exact (bankBottomPaperOccurrenceMultiplier_le_six _ _).trans hySix
  · exact (realization.marker_prime request).pos.ne'



end BankBottomPaperRealization

/-! ## Explicit local geometry and collision freedom -/

theorem yNat_le_bankBottomMarkerLower_of_three_mul_le
    {n : ℕ} (hgeometry : 3 * yNat n ≤ n) (move : BankBottomMove) :
    yNat n ≤ bankBottomMarkerLower n move := by
  cases move <;> simp only [bankBottomMarkerLower] <;> omega

namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)

theorem yNat_lt_marker (hTwoN : 2 * n ≤ M)
    (hgeometry : 3 * yNat n ≤ n)
    (request : ↑(bankBottomPaperRequests n)) :
    yNat n < realization.marker request := by
  have hrow := realization.marker_mem_row hTwoN request
  have hlower : bankBottomMarkerLower n (realization.move request) <
      realization.marker request := (Finset.mem_Ioc.mp hrow).1
  exact (yNat_le_bankBottomMarkerLower_of_three_mul_le
    hgeometry (realization.move request)).trans_lt hlower

/-- Any marker/state/donor value from one request is distinct from every such
value belonging to a different request. -/
theorem occurrenceValue_ne_of_request_ne
    (hTwoN : 2 * n ≤ M) (hySix : 6 ≤ yNat n)
    (hgeometry : 3 * yNat n ≤ n)
    {request request' : ↑(bankBottomPaperRequests n)}
    (hrequest : request ≠ request')
    (kind kind' : BankBottomPaperOccurrenceKind) :
    realization.occurrenceValue request kind ≠
      realization.occurrenceValue request' kind' := by
  intro heq
  have hlarge : 6 < realization.marker request :=
    hySix.trans_lt (realization.yNat_lt_marker hTwoN hgeometry request)
  have hproduct :
      realization.marker request *
          bankBottomPaperOccurrenceMultiplier (realization.move request) kind =
        realization.marker request' *
          bankBottomPaperOccurrenceMultiplier (realization.move request') kind' := by
    simpa only [occurrenceValue, Nat.mul_comm] using heq
  have hmarkers := prime_mul_cofactor_eq_iff_of_marker_large
    (X := 6) (realization.marker_prime request)
      (realization.marker_prime request') hlarge
      (bankBottomPaperOccurrenceMultiplier_pos _ _)
      (bankBottomPaperOccurrenceMultiplier_le_six _ _) hproduct
  exact hrequest (realization.marker_injective hmarkers.1)

theorem carrierValueSets_disjoint_of_request_ne
    (hTwoN : 2 * n ≤ M) (hySix : 6 ≤ yNat n)
    (hgeometry : 3 * yNat n ≤ n)
    {request request' : ↑(bankBottomPaperRequests n)}
    (hrequest : request ≠ request') :
    Disjoint (realization.carrierValueSet request)
      (realization.carrierValueSet request') := by
  rw [Finset.disjoint_left]
  intro occurrence hoccurrence hoccurrence'
  rcases Finset.mem_image.mp hoccurrence with ⟨kind, _hkind, hvalue⟩
  rcases Finset.mem_image.mp hoccurrence' with ⟨kind', _hkind', hvalue'⟩
  exact (realization.occurrenceValue_ne_of_request_ne
    hTwoN hySix hgeometry hrequest kind kind')
      (hvalue.trans hvalue'.symm)

/-- Consequently the actual factor-occurrence sets, which exclude the bare
markers, are pairwise disjoint as well. -/
theorem componentOccurrences_disjoint_of_request_ne
    (hTwoN : 2 * n ≤ M) (hySix : 6 ≤ yNat n)
    (hgeometry : 3 * yNat n ≤ n)
    {request request' : ↑(bankBottomPaperRequests n)}
    (hrequest : request ≠ request') :
    Disjoint (realization.componentOccurrences request)
      (realization.componentOccurrences request') := by
  exact (realization.carrierValueSets_disjoint_of_request_ne
    hTwoN hySix hgeometry hrequest).mono
      (realization.componentOccurrences_subset_carrierValueSet request)
      (realization.componentOccurrences_subset_carrierValueSet request')

/-! ## Relevant markers and marker-to-component uniqueness -/







@[simp] theorem relevantMarker_mem_relevantMarkers
    (request : ↑(bankBottomRelevantPaperRequests n)) :
    realization.marker (bankBottomRelevantRequestToPaperRequest request) ∈
      realization.relevantMarkers := by
  rw [relevantMarkers]
  exact Finset.mem_image.mpr ⟨request, Finset.mem_attach _ _, rfl⟩





@[simp] theorem marker_requestForRelevantMarker
    (marker : ↑realization.relevantMarkers) :
    realization.marker (bankBottomRelevantRequestToPaperRequest
      (realization.requestForRelevantMarker marker)) = marker.1 :=
  (Classical.choose_spec
    (realization.relevantMarker_existsUnique_request marker.property)).1

theorem requestForRelevantMarker_unique
    (marker : ↑realization.relevantMarkers)
    (request : ↑(bankBottomRelevantPaperRequests n))
    (hmarker : realization.marker
      (bankBottomRelevantRequestToPaperRequest request) = marker.1) :
    request = realization.requestForRelevantMarker marker := by
  exact realization.relevantMarkerMap_injective
    (hmarker.trans (realization.marker_requestForRelevantMarker marker).symm)



@[simp] theorem relevantMarkerIncidentStateCores_of_request
    (request : ↑(bankBottomRelevantPaperRequests n)) :
    realization.relevantMarkerIncidentStateCores
        ⟨realization.marker (bankBottomRelevantRequestToPaperRequest request),
          realization.relevantMarker_mem_relevantMarkers request⟩ =
      realization.incidentStateCores
        (bankBottomRelevantRequestToPaperRequest request) := by
  unfold relevantMarkerIncidentStateCores
  have hrequest : realization.requestForRelevantMarker
      ⟨realization.marker (bankBottomRelevantRequestToPaperRequest request),
        realization.relevantMarker_mem_relevantMarkers request⟩ = request := by
    symm
    exact realization.requestForRelevantMarker_unique _ request rfl
  rw [hrequest]







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





/-- The computational definition has the expected mathematical meaning. -/
theorem isPowerOfTwo_iff (m : ℕ) :
    IsPowerOfTwo m ↔ ∃ k : ℕ, m = 2 ^ k := by
  constructor
  · intro h
    exact ⟨Nat.log 2 m, h⟩
  · rintro ⟨k, rfl⟩
    simp [IsPowerOfTwo, Nat.log_pow]

/-- Above the bottom range, the predecessor of a power of two is not itself
a power of two. -/
theorem pred_not_powerOfTwo_of_powerOfTwo {m : ℕ}
    (hm : IsPowerOfTwo m) (hm5 : 5 ≤ m) :
    ¬ IsPowerOfTwo (m - 1) := by
  obtain ⟨k, hk⟩ := (isPowerOfTwo_iff m).mp hm
  rw [isPowerOfTwo_iff]
  rintro ⟨l, hl⟩
  rw [hk] at hm5 hl
  cases k with
  | zero => norm_num at hm5
  | succ k =>
      cases l with
      | zero =>
          norm_num at hl
          omega
      | succ l =>
          have hkmod : (2 ^ Nat.succ k) % 2 = 0 := by
            simp [pow_succ]
          have hlmod : (2 ^ Nat.succ l) % 2 = 0 := by
            simp [pow_succ]
          have hkpos : 0 < 2 ^ Nat.succ k := by positivity
          have hpredmod : (2 ^ Nat.succ k - 1) % 2 = 1 := by omega
          have hmod := congrArg (fun x : ℕ ↦ x % 2) hl
          omega











theorem largeCoreCeil_ge_five {q : ℕ} (hq : 6 ≤ q) :
    5 ≤ largeCoreCeil q := by
  simp [largeCoreCeil, Nat.ceilDiv_eq_add_pred_div]
  omega

/-- The branch correction always produces a non-power. -/
theorem largeCoreStep_not_powerOfTwo {q : ℕ} (hq : 6 ≤ q) :
    ¬ IsPowerOfTwo (largeCoreStep q) := by
  unfold largeCoreStep
  split
  next h =>
    exact pred_not_powerOfTwo_of_powerOfTwo h (largeCoreCeil_ge_five hq)
  next h => exact h

/-- The large-core rule never drops below the terminal core `5`. -/
theorem largeCoreStep_ge_five {q : ℕ} (hq : 6 ≤ q) :
    5 ≤ largeCoreStep q := by
  unfold largeCoreStep
  split
  next h =>
    have hceil := largeCoreCeil_ge_five hq
    have hne : largeCoreCeil q ≠ 5 := by
      intro heq
      rw [heq] at h
      exact (by decide : ¬ IsPowerOfTwo 5) h
    omega
  next _ => exact largeCoreCeil_ge_five hq



/-- Exact lower cross-multiplication for
`largeCoreStep q ≥ 4q/5 - 1`. -/
theorem largeCoreStep_cross_lower {q : ℕ} (hq : 6 ≤ q) :
    4 * q ≤ 5 * largeCoreStep q + 5 := by
  have hceil : 4 * q ≤ 5 * largeCoreCeil q := by
    rw [largeCoreCeil]
    exact (ceilDiv_le_iff_le_mul (a := 5) (b := 4 * q)
      (c := (4 * q) ⌈/⌉ 5) (by norm_num)).mp le_rfl
  unfold largeCoreStep
  split
  next _ =>
    have := largeCoreCeil_ge_five hq
    omega
  next _ => omega





/-- Exact integer form of the strict `17/20` contraction. -/
theorem largeCoreStep_cross_seventeen {q : ℕ} (hq : 21 ≤ q) :
    20 * largeCoreStep q < 17 * q := by
  have h := largeCoreStep_cross_upper q
  omega









/-- Complete large-cell algebra.  The source non-power hypothesis is retained
explicitly because it is the induction invariant of the paper's path. -/
theorem largeCoreStep_spec {Q : ℚ} {q : ℕ}
    (hQ : 20 < Q) (hq : 6 ≤ q) (hqNonpower : ¬ IsPowerOfTwo q)
    (hcell : CoreInGeometricCell Q q) :
    ¬ IsPowerOfTwo q ∧
      ¬ IsPowerOfTwo (largeCoreStep q) ∧
      5 ≤ largeCoreStep q ∧
      largeCoreStep q < q ∧
      InGeometricDescentCell Q q (largeCoreStep q) ∧
      4 * q ≤ 5 * largeCoreStep q + 5 ∧
      5 * largeCoreStep q < 4 * q + 5 ∧
      20 * largeCoreStep q < 17 * q := by
  have hq20Q : (20 : ℚ) < q := hQ.trans hcell.1
  have hq20 : 20 < q := by exact_mod_cast hq20Q
  have hq21 : 21 ≤ q := by omega
  have hlower := largeCoreStep_cross_lower hq
  have hlowerQ : (4 : ℚ) * q ≤ 5 * largeCoreStep q + 5 := by
    exact_mod_cast hlower
  have hbCell : 3 * Q / 4 < (largeCoreStep q : ℚ) := by
    linarith [hcell.1]
  exact ⟨hqNonpower, largeCoreStep_not_powerOfTwo hq,
    largeCoreStep_ge_five hq, largeCoreStep_lt_self hq,
    ⟨hcell, hbCell⟩, hlower, largeCoreStep_cross_upper q,
    largeCoreStep_cross_seventeen hq21⟩





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















 theorem cross_iff_rational_cell
    (N D q b : ℕ) (hD : 0 < D) :
    (N < q * D ∧ 3 * q * D ≤ 4 * N ∧ 3 * N < 4 * b * D) ↔
      (N : ℚ) / D < q ∧
        (q : ℚ) ≤ 4 * ((N : ℚ) / D) / 3 ∧
        3 * ((N : ℚ) / D) / 4 < b := by
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hthree : (0 : ℚ) < 3 := by norm_num
  have hfour : (0 : ℚ) < 4 := by norm_num
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    have h₁Q : (N : ℚ) < q * D := by exact_mod_cast h₁
    have h₂Q : (3 : ℚ) * q * D ≤ 4 * N := by exact_mod_cast h₂
    have h₃Q : (3 : ℚ) * N < 4 * b * D := by exact_mod_cast h₃
    refine ⟨(div_lt_iff₀ hDQ).2 ?_, ?_, ?_⟩
    · simpa only using h₁Q
    · apply (le_div_iff₀ hthree).2
      rw [show (4 : ℚ) * (N / D) = (4 * N) / D by ring]
      apply (le_div_iff₀ hDQ).2
      ring_nf at h₂Q ⊢
      exact h₂Q
    · apply (div_lt_iff₀ hfour).2
      rw [show (3 : ℚ) * (N / D) = (3 * N) / D by ring]
      apply (div_lt_iff₀ hDQ).2
      ring_nf at h₃Q ⊢
      exact h₃Q
  · rintro ⟨h₁, h₂, h₃⟩
    have h₁Q : (N : ℚ) < q * D := (div_lt_iff₀ hDQ).1 h₁
    have h₂Q : (3 : ℚ) * q * D ≤ 4 * N := by
      have h₂a := (le_div_iff₀ hthree).1 h₂
      rw [show (4 : ℚ) * (N / D) = (4 * N) / D by ring] at h₂a
      have h₂b := (le_div_iff₀ hDQ).1 h₂a
      ring_nf at h₂b ⊢
      exact h₂b
    have h₃Q : (3 : ℚ) * N < 4 * b * D := by
      have h₃a := (div_lt_iff₀ hfour).1 h₃
      rw [show (3 : ℚ) * (N / D) = (3 * N) / D by ring] at h₃a
      have h₃b := (div_lt_iff₀ hDQ).1 h₃a
      ring_nf at h₃b ⊢
      exact h₃b
    exact ⟨by exact_mod_cast h₁Q, by exact_mod_cast h₂Q,
      by exact_mod_cast h₃Q⟩

/-- The kernel-reducible cross-products are exactly the paper's literal
rational cell inequalities. -/
theorem inSmallGeometricDescentCellCross_iff
    (scale : SmallDescentScale) (q b : ℕ) :
    InSmallGeometricDescentCellCross scale q b ↔
      InSmallGeometricDescentCell scale q b := by
  unfold InSmallGeometricDescentCellCross InSmallGeometricDescentCell
    smallDescentScaleValue
  exact cross_iff_rational_cell _ _ q b (by
    cases scale <;> decide)























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











/-- The shrunken cofactor window `[7Q/5, 29Q/20]` used for bulk supply. -/
def InOrdinaryBankBulkDonorWindow (Q : ℚ) (u : ℕ) : Prop :=
  7 * Q ≤ 5 * (u : ℚ) ∧
    20 * (u : ℚ) ≤ 29 * Q





/-- A bulk occurrence only asks for the shrunken donor window and the actual
tail occurrence.  When `M ≤ 21n/10`, its marker automatically lies in
`I_Q`, so it belongs to the full relation. -/
def IsOrdinaryBankBulkPair
    (n M : ℕ) (Q : ℚ) (pair : ℕ × ℕ) : Prop :=
  0 < Q ∧
    pair.1.Prime ∧
    0 < pair.2 ∧
    InOrdinaryBankBulkDonorWindow Q pair.2 ∧
    pair.2 ∈ Nat.smoothNumbers (yNat n + 1) ∧
    2 * n < pair.1 * pair.2 ∧
    pair.1 * pair.2 ≤ M





/-- The finite bulk relation used to prove supply. -/
def bankOrdinaryBulkRelation
    (n M : ℕ) (Q : ℚ) : Finset (ℕ × ℕ) :=
  by
    classical
    exact (ordinaryBankPairBox M).filter (IsOrdinaryBankBulkPair n M Q)

 theorem pair_mem_box_of_product_le
    {P u M : ℕ} (hP : 0 < P) (hu : 0 < u) (hPu : P * u ≤ M) :
    (P, u) ∈ ordinaryBankPairBox M := by
  have hPle : P ≤ P * u := Nat.le_mul_of_pos_right P hu
  have hule : u ≤ P * u := by
    simpa only [Nat.mul_comm] using Nat.le_mul_of_pos_right u hP
  simp only [ordinaryBankPairBox, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨hP, hPle.trans hPu⟩, ⟨hu, hule.trans hPu⟩⟩

@[simp] theorem mem_bankOrdinaryEligibleRelation
    {n M P u : ℕ} {Q : ℚ} :
    (P, u) ∈ bankOrdinaryEligibleRelation n M Q ↔
      IsOrdinaryBankEligiblePair n M Q (P, u) := by
  classical
  constructor
  · exact fun h ↦ (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨pair_mem_box_of_product_le h.2.1.pos h.2.2.1 h.2.2.2.2.2.2.2,
      h⟩

@[simp] theorem mem_bankOrdinaryBulkRelation
    {n M P u : ℕ} {Q : ℚ} :
    (P, u) ∈ bankOrdinaryBulkRelation n M Q ↔
      IsOrdinaryBankBulkPair n M Q (P, u) := by
  classical
  constructor
  · exact fun h ↦ (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨pair_mem_box_of_product_le h.2.1.pos h.2.2.1 h.2.2.2.2.2.2,
      h⟩







/-! ## The five exceptional fixed donors -/

/-- The five fixed cofactors in the small-scale table of Section 5.3. -/
def bankOrdinarySmallDonor : SmallDescentScale → ℕ
  | .one => 8
  | .two => 10
  | .three => 13
  | .four => 17
  | .five => 23











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





@[simp] theorem bankOrdinaryCoreStep_five :
    bankOrdinaryCoreStep 5 = 5 := by
  simp [bankOrdinaryCoreStep]





theorem bankSmallCoreStep_certified
    {q : ℕ} (hq6 : 6 ≤ q) (hq22 : q ≤ 22)
    (hqPower : ¬ IsPowerOfTwo q) :
    IsCertifiedSmallDescentEntry (smallDescentScaleForSource q)
      q (bankSmallCoreStep q) := by
  have hq8 : q ≠ 8 := by
    rintro rfl
    exact hqPower (by decide)
  have hq16 : q ≠ 16 := by
    rintro rfl
    exact hqPower (by decide)
  interval_cases q <;> first | contradiction | decide





/-! ## Exact indexing of the rational geometric grid -/







theorem bankOrdinaryScaleIndex_upper (q : ℕ) :
    (q : ℚ) ≤ 4 * bankOrdinaryScale (bankOrdinaryScaleIndex q) / 3 := by
  exact Nat.find_spec (bankOrdinaryScaleIndex_exists q)

theorem bankOrdinaryScaleIndex_cell
    {q : ℕ} (hq : 5 ≤ q) :
    CoreInGeometricCell (bankOrdinaryScale (bankOrdinaryScaleIndex q)) q := by
  refine ⟨?_, bankOrdinaryScaleIndex_upper q⟩
  by_cases hzero : bankOrdinaryScaleIndex q = 0
  · rw [hzero]
    norm_num [bankOrdinaryScale]
    exact_mod_cast hq
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hminimal : ¬ (q : ℚ) ≤ 4 * bankOrdinaryScale j / 3 := by
      intro hbound
      have hle : bankOrdinaryScaleIndex q ≤ j :=
        Nat.find_min' (bankOrdinaryScaleIndex_exists q) hbound
      rw [hj] at hle
      omega
    rw [hj, bankOrdinaryScale_succ]
    exact lt_of_not_ge (by simpa only [mul_assoc] using hminimal)

theorem bankOrdinaryScale_strictMono : StrictMono bankOrdinaryScale := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [bankOrdinaryScale_succ]
  have hpos := bankOrdinaryScale_pos j
  linarith

theorem bankOrdinaryScale_mono : Monotone bankOrdinaryScale :=
  bankOrdinaryScale_strictMono.monotone

theorem bankOrdinaryScaleIndex_ge_six
    {q : ℕ} (hq : 23 ≤ q) :
    6 ≤ bankOrdinaryScaleIndex q := by
  by_contra h
  have hindex : bankOrdinaryScaleIndex q ≤ 5 := by omega
  have hscale := bankOrdinaryScale_mono hindex
  have hupper := bankOrdinaryScaleIndex_upper q
  have hqQ : (23 : ℚ) ≤ q := by exact_mod_cast hq
  simp only [bankOrdinaryScale] at hupper
  norm_num [bankOrdinaryScale] at hscale
  linarith

theorem twenty_lt_bankOrdinaryScale_of_six_le
    {j : ℕ} (hj : 6 ≤ j) :
    (20 : ℚ) < bankOrdinaryScale j := by
  have hscale := bankOrdinaryScale_mono hj
  norm_num [bankOrdinaryScale] at hscale ⊢
  linarith



/-! ## The scale and certificate carried by every component -/



theorem smallDescentScaleValue_eq_bankOrdinaryScale
    (scale : SmallDescentScale) :
    smallDescentScaleValue scale =
      bankOrdinaryScale (smallDescentScaleIndex scale) := by
  cases scale <;>
    norm_num [smallDescentScaleValue, smallDescentScaleNumerator,
      smallDescentScaleDenominator, smallDescentScaleIndex,
      bankOrdinaryScale]

theorem one_le_smallDescentScaleIndex (scale : SmallDescentScale) :
    1 ≤ smallDescentScaleIndex scale := by
  cases scale <;> decide





theorem one_le_bankOrdinaryComponentScaleIndex
    {q : ℕ} (_hq : 6 ≤ q) :
    1 ≤ bankOrdinaryComponentScaleIndex q := by
  by_cases hq22 : q ≤ 22
  · rw [bankOrdinaryComponentScaleIndex, if_pos hq22]
    exact one_le_smallDescentScaleIndex _
  · rw [bankOrdinaryComponentScaleIndex, if_neg hq22]
    exact (show 1 ≤ bankOrdinaryScaleIndex q by
      have := bankOrdinaryScaleIndex_ge_six (show 23 ≤ q by omega)
      omega)



theorem bankOrdinaryCoreStep_spec
    {q : ℕ} (hq : 6 ≤ q) (hqPower : ¬ IsPowerOfTwo q) :
    IsBankOrdinaryCoreComponent q (bankOrdinaryCoreStep q) := by
  by_cases hq22 : q ≤ 22
  · have hentry := bankSmallCoreStep_certified hq hq22 hqPower
    have hstep : bankOrdinaryCoreStep q = bankSmallCoreStep q := by
      rw [bankOrdinaryCoreStep, if_neg (by omega), if_pos hq22]
    have hcellSmall : InSmallGeometricDescentCell
        (smallDescentScaleForSource q) q (bankSmallCoreStep q) :=
      (inSmallGeometricDescentCellCross_iff _ _ _).mp hentry.2.2.2.2.2
    rw [IsBankOrdinaryCoreComponent]
    refine ⟨hq, hqPower, ?_, ?_, ?_, rfl, ?_⟩
    · simpa only [hstep] using hentry.2.2.1
    · simpa only [hstep] using hentry.2.2.2.1
    · simpa only [hstep] using hentry.2.2.2.2.1
    · rw [bankOrdinaryComponentScaleIndex, if_pos hq22,
        ← smallDescentScaleValue_eq_bankOrdinaryScale]
      rcases hcellSmall with ⟨hsourceLower, hsourceUpper, htargetLower⟩
      rw [InGeometricDescentCell, CoreInGeometricCell, hstep]
      exact ⟨⟨hsourceLower, hsourceUpper⟩, htargetLower⟩
  · have hq23 : 23 ≤ q := by omega
    have hindex := bankOrdinaryScaleIndex_ge_six hq23
    have hQ := twenty_lt_bankOrdinaryScale_of_six_le hindex
    have hcell := bankOrdinaryScaleIndex_cell (show 5 ≤ q by omega)
    have hlarge := largeCoreStep_spec hQ hq hqPower hcell
    have hstep := bankOrdinaryCoreStep_eq_largeCoreStep (by omega : 22 < q)
    rw [IsBankOrdinaryCoreComponent]
    refine ⟨hq, hqPower, ?_, ?_, ?_, rfl, ?_⟩
    · simpa only [hstep] using hlarge.2.1
    · simpa only [hstep] using hlarge.2.2.1
    · simpa only [hstep] using hlarge.2.2.2.1
    · rw [bankOrdinaryComponentScaleIndex, if_neg hq22]
      simpa only [hstep] using hlarge.2.2.2.2.1

theorem prime_not_isPowerOfTwo_of_five_le
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ IsPowerOfTwo p := by
  rw [isPowerOfTwo_iff]
  rintro ⟨k, hk⟩
  have hdata := hp.pow_eq_iff.mp hk.symm
  omega

/-! ## A literal finite terminating path -/









theorem bankOrdinaryCoreSources_of_le_five
    {q : ℕ} (hq : q ≤ 5) :
    bankOrdinaryCoreSources q = ∅ := by
  rw [bankOrdinaryCoreSources]
  simp [hq]

theorem bankOrdinaryCoreSources_of_six_le
    {q : ℕ} (hq : 6 ≤ q) :
    bankOrdinaryCoreSources q =
      insert q (bankOrdinaryCoreSources (bankOrdinaryCoreStep q)) := by
  rw [bankOrdinaryCoreSources]
  rw [if_neg (by omega)]









theorem bankOrdinaryCoreSource_le_start
    {q s : ℕ} (hs : s ∈ bankOrdinaryCoreSources q) :
    s ≤ q := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      by_cases hq5 : q ≤ 5
      · simp [bankOrdinaryCoreSources_of_le_five hq5] at hs
      · have hq6 : 6 ≤ q := by omega
        rw [bankOrdinaryCoreSources_of_six_le hq6] at hs
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact le_rfl
        · exact (ih _ (bankOrdinaryCoreStep_lt_self (by omega)) hs).trans
            (bankOrdinaryCoreStep_lt_self (by omega)).le



/-- Every source reached from a legal starting core carries the complete
component certificate, including its actual grid cell and actual target. -/
theorem bankOrdinaryCoreSource_spec
    {q s : ℕ} (hq : 5 ≤ q) (hqPower : ¬ IsPowerOfTwo q)
    (hs : s ∈ bankOrdinaryCoreSources q) :
    IsBankOrdinaryCoreComponent s (bankOrdinaryCoreStep s) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      by_cases hq5 : q ≤ 5
      · simp [bankOrdinaryCoreSources_of_le_five hq5] at hs
      · have hq6 : 6 ≤ q := by omega
        have hspec := bankOrdinaryCoreStep_spec hq6 hqPower
        rw [bankOrdinaryCoreSources_of_six_le hq6] at hs
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact hspec
        · exact ih (bankOrdinaryCoreStep q) hspec.2.2.2.2.1
            hspec.2.2.2.1 hspec.2.2.1 hs

/-! ## The actual finite path telescopes -/















/-- The actual component sources of one path routed to grid index `j`. -/
def bankOrdinaryCoreSourcesAtScale (q j : ℕ) : Finset ℕ :=
  (bankOrdinaryCoreSources q).filter fun s ↦
    bankOrdinaryComponentScaleIndex s = j









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryDonorSupply -/
section


/-!
# Analytic supply for the ordinary bank

This file supplies the analytic half of the ordinary marker--donor argument.
The only prime-number input is the already audited cumulative estimate
`FriableAsymptotic.exists_primeLogSumUpTo_error_bound 3`.  We first turn its
two endpoint errors into a lower bound for an actual finite prime interval.
We then count the literal smooth donor window, sum the resulting occurrences,
and pass the exact marker-fiber bound through
`bankOccurrenceCeilDiv_le_markerCount`.

No asymptotic assertion is stored in a structure or accepted as a field.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.FriableAsymptotic

noncomputable section

/-! ## A cumulative-theta short-interval lemma -/

/-- The actual finite prime interval `(A,B]`. -/
def bankPrimeInterval (A B : ℕ) : Finset ℕ :=
  (Finset.Ioc A B).filter Nat.Prime









/-! ## The literal smooth donor window -/

/-- All integers in the shrunken rational donor window. -/
def bankOrdinaryBulkDonorIntegers (Q : ℚ) : Finset ℕ :=
  Finset.Icc ⌈7 * Q / 5⌉₊ ⌊29 * Q / 20⌋₊

/-- The actual `yNat n`-smooth integers in the shrunken donor window. -/
def bankOrdinarySmoothBulkDonors (n : ℕ) (Q : ℚ) : Finset ℕ :=
  (bankOrdinaryBulkDonorIntegers Q).filter
    fun u ↦ u ∈ Nat.smoothNumbers (yNat n + 1)

@[simp] theorem mem_bankOrdinaryBulkDonorIntegers
    {Q : ℚ} {u : ℕ} (hQ : 0 ≤ Q) :
    u ∈ bankOrdinaryBulkDonorIntegers Q ↔
      InOrdinaryBankBulkDonorWindow Q u := by
  simp only [bankOrdinaryBulkDonorIntegers, Finset.mem_Icc,
    InOrdinaryBankBulkDonorWindow]
  constructor
  · rintro ⟨hlower, hupper⟩
    have ha : 7 * Q / 5 ≤ (u : ℚ) :=
      (Nat.le_ceil (7 * Q / 5)).trans (by exact_mod_cast hlower)
    have hupperQ : (u : ℚ) ≤ (⌊29 * Q / 20⌋₊ : ℚ) := by
      exact_mod_cast hupper
    have hb : (u : ℚ) ≤ 29 * Q / 20 :=
      hupperQ.trans
        (Nat.floor_le (by positivity : 0 ≤ 29 * Q / 20))
    constructor <;> linarith
  · rintro ⟨hlower, hupper⟩
    constructor
    · apply Nat.ceil_le.mpr
      linarith
    · apply Nat.le_floor
      linarith

@[simp] theorem mem_bankOrdinarySmoothBulkDonors
    {n : ℕ} {Q : ℚ} {u : ℕ} (hQ : 0 ≤ Q) :
    u ∈ bankOrdinarySmoothBulkDonors n Q ↔
      InOrdinaryBankBulkDonorWindow Q u ∧
        u ∈ Nat.smoothNumbers (yNat n + 1) := by
  simp [bankOrdinarySmoothBulkDonors,
    mem_bankOrdinaryBulkDonorIntegers hQ]













/-! ## Summing one-donor prime intervals -/

/-- Prime markers whose product with a fixed donor lies in `(2n,M]`. -/
def bankOrdinaryPrimeChoices (n M u : ℕ) : Finset ℕ :=
  bankPrimeInterval ((2 * n) / u) (M / u)

@[simp] theorem mem_bankOrdinaryPrimeChoices
    {n M u P : ℕ} (hu : 0 < u) :
    P ∈ bankOrdinaryPrimeChoices n M u ↔
      P.Prime ∧ 2 * n < P * u ∧ P * u ≤ M := by
  simp only [bankOrdinaryPrimeChoices, bankPrimeInterval,
    Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlower, hupper⟩, hprime⟩
    exact ⟨hprime,
      (by simpa only [Nat.mul_comm] using
        (Nat.div_lt_iff_lt_mul hu).1 hlower),
      (by simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hu).1 hupper)⟩
  · rintro ⟨hprime, hlower, hupper⟩
    exact ⟨⟨(Nat.div_lt_iff_lt_mul hu).2 (by
      simpa only [Nat.mul_comm] using hlower),
      (Nat.le_div_iff_mul_le hu).2 (by
        simpa only [Nat.mul_comm] using hupper)⟩, hprime⟩





/-! ## Uniform one-donor geometry -/



















/-! ## Marker supply from the exact fiber bound -/

/-- A convenient integral cap for the donor multiplicity of one marker. -/
def bankOrdinaryMultiplicityCap (c : ℝ) (n : ℕ) (Q : ℚ) : ℕ :=
  ⌈2 * c * (Q : ℝ) / Real.log (n : ℝ) + 2⌉₊









/-! ## The five fixed nonbottom scales -/

















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















def bankOrdinaryPoolDemand
    (n : ℕ) (pool : BankOrdinaryOrientationPool) : ℕ :=
  (bankOrdinaryRequestsInPool n pool).card

/-- Every materialized request is an actual certified component of its
prime's terminating path. -/
theorem bankOrdinaryPaperRequest_component_spec
    {n : ℕ} (request : BankOrdinaryPaperRequest n) :
    IsBankOrdinaryCoreComponent
      (bankOrdinaryPaperRequestSource request)
      (bankOrdinaryPaperRequestTarget request) := by
  let p : ↑(bankRoundingPrimeSupport n) := request.1.1
  have hp := bankRoundingPrimeSupport_prime p.property
  have hp6 : 6 ≤ p.1 := by
    by_contra h
    have hp5 : p.1 ≤ 5 := by omega
    let source : ℕ := request.2.1
    have hsource : source ∈ bankOrdinaryCoreSources p.1 :=
      request.2.property
    rw [bankOrdinaryCoreSources_of_le_five hp5] at hsource
    simp at hsource
  have hpPower : ¬ IsPowerOfTwo p.1 :=
    prime_not_isPowerOfTwo_of_five_le hp (by omega)
  exact bankOrdinaryCoreSource_spec (show 5 ≤ p.1 by omega) hpPower
    request.2.property

theorem bankOrdinaryPaperRequest_scale_le_yNat
    {n : ℕ} (request : BankOrdinaryPaperRequest n) :
    bankOrdinaryScale (bankOrdinaryPaperRequestPool n request).1 ≤
      (yNat n : ℚ) := by
  have hspec := bankOrdinaryPaperRequest_component_spec request
  have hsourcePrime : request.1.1.1 ≤ yNat n :=
    bankRoundingPrimeSupport_le_yNat request.1.1.property
  have hsourceLe := bankOrdinaryCoreSource_le_start request.2.property
  have hscaleLt :
      bankOrdinaryScale (bankOrdinaryPaperRequestPool n request).1 <
        (bankOrdinaryPaperRequestSource request : ℚ) :=
    hspec.2.2.2.2.2.2.1.1
  have hsourceY : bankOrdinaryPaperRequestSource request ≤ yNat n :=
    hsourceLe.trans hsourcePrime
  exact hscaleLt.le.trans (by exact_mod_cast hsourceY)

/-! ## Exact request-fiber cardinality -/

 def bankOrdinaryPaperRequestFiberEquiv
    (n : ℕ) (pool : BankOrdinaryOrientationPool) :
    ↑(bankOrdinaryRequestsInPool n pool) ≃
      Σ p : ↑(bankRoundingPrimeSupport n),
        Fin (bankRoundingBetaOnSupport n p) ×
          ↑(bankOrdinaryCoreSourcesAtScale p.1 pool.1) where
  toFun request :=
    ⟨request.1.1.1,
      (match request.1.1.2 with
        | .inl copy => copy
        | .inr copy => copy),
      ⟨request.1.2.1, by
        apply Finset.mem_filter.mpr
        refine ⟨request.1.2.property, ?_⟩
        have hpool := (Finset.mem_filter.mp request.property).2
        exact congrArg Prod.fst hpool⟩⟩
  invFun indexed :=
    ⟨⟨⟨indexed.1,
        match pool.2 with
        | .downward => Sum.inl indexed.2.1
        | .upward => Sum.inr indexed.2.1⟩,
      ⟨indexed.2.2.1, (Finset.mem_filter.mp indexed.2.2.property).1⟩⟩,
      by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases pool with ⟨j, orientation⟩
        cases orientation <;>
          simpa [bankOrdinaryPaperRequestPool,
            bankOrdinaryPaperRequestSource, bankSignedSlotOrientation] using
              (Finset.mem_filter.mp indexed.2.2.property).2⟩
  left_inv request := by
    rcases pool with ⟨j, orientation⟩
    rcases request with ⟨⟨⟨prime, signedCopy⟩, source⟩, hrequest⟩
    have hpool := (Finset.mem_filter.mp hrequest).2
    cases signedCopy with
    | inl copy =>
        have horientation : orientation = .downward := by
          exact (congrArg Prod.snd hpool).symm
        subst orientation
        rfl
    | inr copy =>
        have horientation : orientation = .upward := by
          exact (congrArg Prod.snd hpool).symm
        subst orientation
        rfl
  right_inv indexed := by
    rcases pool with ⟨j, orientation⟩
    rcases indexed with ⟨prime, copy, source⟩
    cases orientation <;> rfl















/-! ## The beta reserve against the worst moving ordinary scale -/

/-- The smallest marker scale among `Q <= yNat`, with a harmless positive
denominator at small `n`. -/
def bankOrdinaryWorstMarkerScale (n : ℕ) : ℝ :=
  secondOrderScale n / max 1 (yNat n : ℝ)

















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



def bankOrdinaryPoolCapacity
    (n M : ℕ) (pool : BankOrdinaryOrientationPool) : ℕ :=
  (bankOrdinaryAvailablePairs n M pool).card

theorem bankOrdinaryAvailablePairs_subset_eligible
    (n M : ℕ) (pool : BankOrdinaryOrientationPool) :
    bankOrdinaryAvailablePairs n M pool ⊆
      bankOrdinaryEligibleRelation n M (bankOrdinaryScale pool.1) := by
  cases pool with
  | mk j orientation =>
      cases orientation
      · exact bankOrientationPoolFirst_subset_eligible _
      · exact bankOrientationPoolSecond_subset_eligible _



 theorem bankOrdinary_markerIntervals_disjoint_ordered
    {n P j k : ℕ} (hjk : j < k)
    (hj : InOrdinaryBankMarkerInterval n (bankOrdinaryScale j) P)
    (hk : InOrdinaryBankMarkerInterval n (bankOrdinaryScale k) P) :
    False := by
  have hsucc : j + 1 ≤ k := by omega
  have hscale := bankOrdinaryScale_mono hsucc
  rw [bankOrdinaryScale_succ] at hscale
  have hP : (0 : ℚ) ≤ P := by positivity
  have hscaleP := mul_le_mul_of_nonneg_right hscale hP
  unfold InOrdinaryBankMarkerInterval at hj hk
  nlinarith

theorem bankOrdinary_markerIntervals_disjoint
    {n P j k : ℕ} (hjk : j ≠ k)
    (hj : InOrdinaryBankMarkerInterval n (bankOrdinaryScale j) P)
    (hk : InOrdinaryBankMarkerInterval n (bankOrdinaryScale k) P) :
    False := by
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · exact bankOrdinary_markerIntervals_disjoint_ordered hjk hj hk
  · exact bankOrdinary_markerIntervals_disjoint_ordered hkj hk hj

/-- Distinct scale/orientation labels give disjoint actual numerical pools. -/
theorem bankOrdinaryAvailablePairs_disjoint
    {n M : ℕ} {pool pool' : BankOrdinaryOrientationPool}
    (hpools : pool ≠ pool') :
    Disjoint (bankOrdinaryAvailablePairs n M pool)
      (bankOrdinaryAvailablePairs n M pool') := by
  rw [Finset.disjoint_left]
  intro pair hpair hpair'
  by_cases hscale : pool.1 = pool'.1
  · have horientation : pool.2 ≠ pool'.2 := by
      intro h
      exact hpools (Prod.ext hscale h)
    rcases pool with ⟨j, orientation⟩
    rcases pool' with ⟨j', orientation'⟩
    simp only at hscale
    subst j'
    cases orientation <;> cases orientation'
    · exact (horientation rfl).elim
    · exact (Finset.disjoint_left.mp
        (bankOrientationPools_disjoint
          (bankOrdinaryEligibleRelation n M (bankOrdinaryScale j))))
            hpair hpair'
    · exact (Finset.disjoint_left.mp
        (bankOrientationPools_disjoint
          (bankOrdinaryEligibleRelation n M (bankOrdinaryScale j))).symm)
            hpair hpair'
    · exact (horientation rfl).elim
  · have heligible := bankOrdinaryAvailablePairs_subset_eligible n M pool hpair
    have heligible' := bankOrdinaryAvailablePairs_subset_eligible n M pool' hpair'
    have hmarker := (mem_bankOrdinaryEligibleRelation.mp heligible).2.2.2.1
    have hmarker' := (mem_bankOrdinaryEligibleRelation.mp heligible').2.2.2.1
    exact bankOrdinary_markerIntervals_disjoint hscale hmarker hmarker'

/-! ## Capacity from the beta reserve -/











/-! ## Finite poolwise matching -/











theorem bankOrdinaryLabelRequest_injective (n : ℕ) :
    Function.Injective (@bankOrdinaryLabelRequest n) := by
  intro request request' heq
  apply Subtype.ext
  exact congrArg (fun labeled ↦ labeled.2.1) heq



theorem BankOrdinaryPoolMatching.slotOfLabeledRequest_mem
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : BankOrdinaryLabeledRequest n) :
    matching.slotOfLabeledRequest request ∈
      bankOrdinaryAvailablePairs n M request.1 :=
  (matching.toEmbedding request.1 request.2).property

theorem BankOrdinaryPoolMatching.slotOfLabeledRequest_injective
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M) :
    Function.Injective matching.slotOfLabeledRequest := by
  rintro ⟨pool, request⟩ ⟨pool', request'⟩ heq
  by_cases hp : pool = pool'
  · subst pool'
    have hembedding : matching.toEmbedding pool request =
        matching.toEmbedding pool request' := by
      apply Subtype.ext
      exact heq
    have hrequest := (matching.toEmbedding pool).injective hembedding
    subst request'
    rfl
  · have hleft : matching.slotOfLabeledRequest ⟨pool, request⟩ ∈
        bankOrdinaryAvailablePairs n M pool :=
      matching.slotOfLabeledRequest_mem ⟨pool, request⟩
    have hright : matching.slotOfLabeledRequest ⟨pool, request⟩ ∈
        bankOrdinaryAvailablePairs n M pool' := by
      rw [heq]
      exact matching.slotOfLabeledRequest_mem ⟨pool', request'⟩
    exact False.elim ((Finset.disjoint_left.mp
      (bankOrdinaryAvailablePairs_disjoint hp)) hleft hright)



theorem BankOrdinaryPoolMatching.matchedPair_mem_available
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    matching.matchedPair request ∈
      bankOrdinaryAvailablePairs n M
        (bankOrdinaryPaperRequestPool n request.1) :=
  matching.slotOfLabeledRequest_mem (bankOrdinaryLabelRequest request)

theorem BankOrdinaryPoolMatching.matchedPair_injective
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M) :
    Function.Injective matching.matchedPair :=
  matching.slotOfLabeledRequest_injective.comp
    (bankOrdinaryLabelRequest_injective n)

theorem BankOrdinaryPoolMatching.matchedPair_eligible
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    matching.matchedPair request ∈
      bankOrdinaryEligibleRelation n M
        (bankOrdinaryScale
          (bankOrdinaryPaperRequestPool n request.1).1) := by
  exact bankOrdinaryAvailablePairs_subset_eligible n M _
    (matching.matchedPair_mem_available request)



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

 theorem bank_yNat_sq_le
    {n : ℕ} (hn : 1 ≤ n) : yNat n * yNat n ≤ n := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  have hyFloorNonneg : (0 : ℝ) ≤ yNat n := by positivity
  have hsq : (yNat n : ℝ) ^ 2 ≤ y n ^ 2 :=
    (sq_le_sq₀ hyFloorNonneg hyNonneg).2 hyFloor
  have hpow : (n : ℝ) ^ (4 / 9 : ℝ) ≤ (n : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnOne
        (by norm_num : (4 / 9 : ℝ) ≤ 1)
  rw [Erdos390.Full.Scale.y_pow_two] at hsq
  have hcast : ((yNat n * yNat n : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    simpa only [pow_two] using hsq.trans hpow
  exact_mod_cast hcast

/-- Multiplying two smooth cofactors by the same nonzero marker preserves
their complete rough signature. -/
theorem completeRoughSignature_marker_mul_smooth_eq
    {y P a b : ℕ} (hP : P ≠ 0)
    (ha : a ∈ Nat.smoothNumbers (y + 1))
    (hb : b ∈ Nat.smoothNumbers (y + 1)) :
    completeRoughSignature y (P * a) =
      completeRoughSignature y (P * b) := by
  ext r
  rw [completeRoughSignature_apply, completeRoughSignature_apply]
  by_cases hry : y < r
  · simp only [hry, if_true]
    have haZero : a.factorization r = 0 := by
      by_cases hr : r.Prime
      · apply Nat.factorization_eq_zero_of_not_dvd
        intro hrDiv
        have hrSmall := (Nat.mem_smoothNumbers').mp ha r hr hrDiv
        omega
      · exact Nat.factorization_eq_zero_of_not_prime _ hr
    have hbZero : b.factorization r = 0 := by
      by_cases hr : r.Prime
      · apply Nat.factorization_eq_zero_of_not_dvd
        intro hrDiv
        have hrSmall := (Nat.mem_smoothNumbers').mp hb r hr hrDiv
        omega
      · exact Nat.factorization_eq_zero_of_not_prime _ hr
    rw [Nat.factorization_mul hP (Nat.ne_zero_of_mem_smoothNumbers ha),
      Nat.factorization_mul hP (Nat.ne_zero_of_mem_smoothNumbers hb),
      Finsupp.add_apply, Finsupp.add_apply, haZero, hbZero]
  · simp [hry]

/-- A product of a prime marker above the smooth cutoff remembers that marker
uniquely. -/
theorem primeMarker_mul_smooth_marker_eq
    {y P P' a a' : ℕ}
    (hP : P.Prime) (hP' : P'.Prime)
    (hPy : y < P) (_hP'y : y < P')
    (_ha : a ∈ Nat.smoothNumbers (y + 1))
    (ha' : a' ∈ Nat.smoothNumbers (y + 1))
    (heq : P * a = P' * a') :
    P = P' := by
  have hdiv : P ∣ P' * a' := by
    rw [← heq]
    exact dvd_mul_right P a
  rcases hP.dvd_mul.mp hdiv with hPP' | hPa'
  · exact (Nat.prime_dvd_prime_iff_eq hP hP').mp hPP'
  · have hsmall := (Nat.mem_smoothNumbers').mp ha' P hP hPa'
    omega



/-! ## Marker injectivity inherited from the orientation pools -/

theorem bankOrdinaryAvailablePairs_subset_markerDonorPairs
    (n M : ℕ) (pool : BankOrdinaryOrientationPool) :
    bankOrdinaryAvailablePairs n M pool ⊆
      bankMarkerDonorPairs
        (bankOrdinaryEligibleRelation n M (bankOrdinaryScale pool.1)) := by
  rcases pool with ⟨j, orientation⟩
  cases orientation
  · exact bankOrientationPoolFirst_subset_pairs _
  · intro pair hpair
    exact (Finset.mem_sdiff.mp hpair).1





theorem BankOrdinaryPoolMatching.matchedMarker_injective
    {n M : ℕ} (matching : BankOrdinaryPoolMatching n M) :
    Function.Injective matching.matchedMarker := by
  intro request request' hmarker
  let pool := bankOrdinaryPaperRequestPool n request.1
  let pool' := bankOrdinaryPaperRequestPool n request'.1
  by_cases hscale : pool.1 = pool'.1
  · let eligible := bankOrdinaryEligibleRelation n M
      (bankOrdinaryScale pool.1)
    have hpair : matching.matchedPair request ∈
        bankMarkerDonorPairs eligible := by
      exact bankOrdinaryAvailablePairs_subset_markerDonorPairs n M pool
        (matching.matchedPair_mem_available request)
    have hpair' : matching.matchedPair request' ∈
        bankMarkerDonorPairs eligible := by
      have hmem := bankOrdinaryAvailablePairs_subset_markerDonorPairs
        n M pool' (matching.matchedPair_mem_available request')
      simpa only [eligible, hscale] using hmem
    have hpairs := bankMarkerDonorPairs_injective_by_marker eligible
      hpair hpair' hmarker
    exact matching.matchedPair_injective hpairs
  · have heligible := matching.matchedPair_eligible request
    have heligible' := matching.matchedPair_eligible request'
    have hcell := (mem_bankOrdinaryEligibleRelation.mp heligible).2.2.2.1
    have hcell' := (mem_bankOrdinaryEligibleRelation.mp heligible').2.2.2.1
    have hcellAt : InOrdinaryBankMarkerInterval n
        (bankOrdinaryScale pool'.1) (matching.matchedMarker request) :=
      Eq.mp
        (congrArg
          (fun P ↦ InOrdinaryBankMarkerInterval n
            (bankOrdinaryScale pool'.1) P) hmarker).symm
        hcell'
    exact False.elim
      (bankOrdinary_markerIntervals_disjoint hscale hcell hcellAt)

/-! ## The public realization object and its actual factors -/



namespace BankOrdinaryPaperRealization









theorem markerDonorPair_mem
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.markerDonorPair request ∈
      bankOrdinaryEligibleRelation n M
        (bankOrdinaryScale
          (bankOrdinaryPaperRequestPool n request.1).1) :=
  R.matching.matchedPair_eligible request

theorem marker_prime
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    (R.marker request).Prime :=
  (mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)).2.1



theorem donorCore_smooth
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.donorCore request ∈ Nat.smoothNumbers (yNat n + 1) :=
  (mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)).2.2.2.2.2.1

theorem sourceCore_le_yNat
    {n M : ℕ} (_R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    bankOrdinaryPaperRequestSource request.1 ≤ yNat n := by
  exact (bankOrdinaryCoreSource_le_start request.1.2.property).trans
    (bankRoundingPrimeSupport_le_yNat request.1.1.1.property)

theorem targetCore_le_yNat
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    bankOrdinaryPaperRequestTarget request.1 ≤ yNat n := by
  have hspec := bankOrdinaryPaperRequest_component_spec request.1
  exact hspec.2.2.2.2.1.le.trans (R.sourceCore_le_yNat request)

theorem sourceCore_smooth
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    bankOrdinaryPaperRequestSource request.1 ∈
      Nat.smoothNumbers (yNat n + 1) := by
  have hspec := bankOrdinaryPaperRequest_component_spec request.1
  have hsourcePos : 0 < bankOrdinaryPaperRequestSource request.1 := by
    have hsourceSix := hspec.1
    omega
  exact Nat.mem_smoothNumbers_of_lt hsourcePos
    (Nat.lt_succ_of_le (R.sourceCore_le_yNat request))

theorem targetCore_smooth
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    bankOrdinaryPaperRequestTarget request.1 ∈
      Nat.smoothNumbers (yNat n + 1) := by
  have hspec := bankOrdinaryPaperRequest_component_spec request.1
  have htargetPos : 0 < bankOrdinaryPaperRequestTarget request.1 := by
    have htargetFive := hspec.2.2.2.1
    omega
  exact Nat.mem_smoothNumbers_of_lt htargetPos
    (Nat.lt_succ_of_le (R.targetCore_le_yNat request))

/-- Every matched marker lies above the complete-signature cutoff. -/
theorem yNat_lt_marker
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    yNat n < R.marker request := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  have hQY := bankOrdinaryPaperRequest_scale_le_yNat request.1
  have hySq := bank_yNat_sq_le R.one_le_n
  by_contra hmarker
  have hmarkerLe : R.marker request ≤ yNat n := by omega
  have hmarkerQ : (0 : ℚ) ≤ R.marker request := by positivity
  have hproduct :
      bankOrdinaryScale (bankOrdinaryPaperRequestPool n request.1).1 *
          (R.marker request : ℚ) ≤
        (yNat n : ℚ) * yNat n := by
    exact mul_le_mul hQY (by exact_mod_cast hmarkerLe) hmarkerQ
      (by positivity : (0 : ℚ) ≤ yNat n)
  have hySqQ : (yNat n : ℚ) * yNat n ≤ n := by
    exact_mod_cast hySq
  have hmarkerLower := heligible.2.2.2.1.1
  nlinarith

/-- Ordinary markers lie strictly below every bottom-row marker scale.  The
first ordinary grid value is `16/3`, and the upper marker inequality at that
scale already forces `3P<n`. -/
theorem three_mul_marker_lt_n
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    3 * R.marker request < n := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  have hspec := bankOrdinaryPaperRequest_component_spec request.1
  have hindex :
      1 ≤ (bankOrdinaryPaperRequestPool n request.1).1 := by
    simpa only [bankOrdinaryPaperRequestPool] using
      one_le_bankOrdinaryComponentScaleIndex hspec.1
  have hscale := bankOrdinaryScale_mono hindex
  have hscaleLower : (16 / 3 : ℚ) ≤
      bankOrdinaryScale (bankOrdinaryPaperRequestPool n request.1).1 := by
    norm_num [bankOrdinaryScale] at hscale ⊢
    exact hscale
  have hmarkerUpper := heligible.2.2.2.1.2
  have hmarkerPos : (0 : ℚ) < R.marker request := by
    exact_mod_cast (R.marker_prime request).pos
  have hbound : (3 : ℚ) * R.marker request < n := by
    nlinarith
  exact_mod_cast hbound

















theorem state_donor_completeRoughSignature_eq
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    completeRoughSignature (yNat n) (R.sourceStateValue request) =
        completeRoughSignature (yNat n) (R.targetStateValue request) ∧
      completeRoughSignature (yNat n) (R.targetStateValue request) =
        completeRoughSignature (yNat n) (R.donorValue request) := by
  constructor
  · exact completeRoughSignature_marker_mul_smooth_eq
      (R.marker_prime request).ne_zero
      (R.sourceCore_smooth request) (R.targetCore_smooth request)
  · exact completeRoughSignature_marker_mul_smooth_eq
      (R.marker_prime request).ne_zero
      (R.targetCore_smooth request) (R.donorCore_smooth request)

theorem marker_injective
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M) :
    Function.Injective R.marker :=
  R.matching.matchedMarker_injective





@[simp] theorem marker_mem_markers
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.marker request ∈ R.markers := by
  simp [markers]









@[simp] theorem marker_requestForMarker
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (P : ↑R.markers) :
    R.marker (R.requestForMarker P) = P.1 :=
  Classical.choose_spec (R.exists_request_for_marker P)

theorem requestForMarker_unique
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (P : ↑R.markers)
    (request : ↑(bankOrdinaryPaperRequests n))
    (hmarker : R.marker request = P.1) :
    request = R.requestForMarker P := by
  apply R.marker_injective
  exact hmarker.trans (R.marker_requestForMarker P).symm

/-- The path-source cofactor canonically attached to a realized marker. -/
def markerSourceCore
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (P : ↑R.markers) : ℕ :=
  bankOrdinaryPaperRequestSource (R.requestForMarker P).1

@[simp] theorem markerSourceCore_of_request
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.markerSourceCore
        ⟨R.marker request, R.marker_mem_markers request⟩ =
      bankOrdinaryPaperRequestSource request.1 := by
  unfold markerSourceCore
  have hrequest :
      R.requestForMarker
          ⟨R.marker request, R.marker_mem_markers request⟩ = request := by
    symm
    exact R.requestForMarker_unique _ request rfl
  rw [hrequest]





/-! ## The three actual occurrences and global collision-freedom -/













@[simp] theorem occurrenceValue_sourceState
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.occurrenceValue request .sourceState = R.sourceStateValue request := rfl

@[simp] theorem occurrenceValue_targetState
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.occurrenceValue request .targetState = R.targetStateValue request := rfl

@[simp] theorem occurrenceValue_donor
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.occurrenceValue request .donor = R.donorValue request := rfl



theorem occurrenceCofactor_smooth
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n))
    (kind : BankOrdinaryPaperOccurrenceKind) :
    R.occurrenceCofactor request kind ∈
      Nat.smoothNumbers (yNat n + 1) := by
  cases kind
  · exact R.sourceCore_smooth request
  · exact R.targetCore_smooth request
  · exact R.donorCore_smooth request

theorem occurrenceValue_eq_marker_implies_request_eq
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    {request request' : ↑(bankOrdinaryPaperRequests n)}
    {kind kind' : BankOrdinaryPaperOccurrenceKind}
    (heq : R.occurrenceValue request kind =
      R.occurrenceValue request' kind') :
    request = request' := by
  have hmarker : R.marker request = R.marker request' :=
    primeMarker_mul_smooth_marker_eq
      (R.marker_prime request) (R.marker_prime request')
      (R.yNat_lt_marker request) (R.yNat_lt_marker request')
      (R.occurrenceCofactor_smooth request kind)
      (R.occurrenceCofactor_smooth request' kind') heq
  exact R.marker_injective hmarker

theorem occurrenceValue_ne_of_request_ne
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    {request request' : ↑(bankOrdinaryPaperRequests n)}
    (hrequest : request ≠ request')
    (kind kind' : BankOrdinaryPaperOccurrenceKind) :
    R.occurrenceValue request kind ≠
      R.occurrenceValue request' kind' := by
  intro heq
  exact hrequest (R.occurrenceValue_eq_marker_implies_request_eq heq)



theorem occurrenceValue_mem_componentOccurrences
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n))
    (kind : BankOrdinaryPaperOccurrenceKind) :
    R.occurrenceValue request kind ∈ R.componentOccurrences request := by
  exact Finset.mem_image.mpr ⟨kind, Finset.mem_univ _, rfl⟩





theorem componentOccurrences_disjoint
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    {request request' : ↑(bankOrdinaryPaperRequests n)}
    (hrequest : request ≠ request') :
    Disjoint (R.componentOccurrences request)
      (R.componentOccurrences request') := by
  rw [Finset.disjoint_left]
  intro value hvalue hvalue'
  rw [componentOccurrences, Finset.mem_image] at hvalue hvalue'
  obtain ⟨kind, _hkind, rfl⟩ := hvalue
  obtain ⟨kind', _hkind', heq⟩ := hvalue'
  exact R.occurrenceValue_ne_of_request_ne hrequest kind kind' heq.symm



/-! ## Realized component and signed-slot changes -/























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





namespace BankPaperRealization

def marker
    {n M : ℕ} (R : BankPaperRealization n M) :
    BankPaperMarkerRequest n → ℕ
  | .inl request =>
      R.bottom.marker (bankBottomRelevantRequestToPaperRequest request)
  | .inr request => R.ordinary.marker request

/-- The two marker ranges are separated before any factorization argument is
needed. -/
theorem ordinaryMarker_lt_bottomMarker
    {n M : ℕ} (R : BankPaperRealization n M)
    (ordinaryRequest : ↑(bankOrdinaryPaperRequests n))
    (bottomRequest : ↑(bankBottomPaperRequests n)) :
    R.ordinary.marker ordinaryRequest <
      R.bottom.marker bottomRequest := by
  have hordinary :=
    R.ordinary.three_mul_marker_lt_n ordinaryRequest
  have hbottom := R.bottom.n_lt_three_mul_marker
    R.ordinary.two_mul_n_le_M bottomRequest
  omega













/-! ## Cross-family actual occurrence disjointness -/

/-- One ordinary actual occurrence cannot equal any named bottom carrier
value.  The bottom carrier is intentionally slightly larger than its actual
factor set, so this theorem immediately covers every actual bottom factor. -/
theorem ordinaryOccurrence_ne_bottomCarrier
    {n M : ℕ} (R : BankPaperRealization n M)
    (ordinaryRequest : ↑(bankOrdinaryPaperRequests n))
    (ordinaryKind : BankOrdinaryPaperOccurrenceKind)
    (bottomRequest : ↑(bankBottomPaperRequests n))
    (bottomKind : BankBottomPaperOccurrenceKind) :
    R.ordinary.occurrenceValue ordinaryRequest ordinaryKind ≠
      R.bottom.occurrenceValue bottomRequest bottomKind := by
  intro heq
  have hbottomSmooth :
      bankBottomPaperOccurrenceMultiplier
          (R.bottom.move bottomRequest) bottomKind ∈
        Nat.smoothNumbers (yNat n + 1) := by
    apply Nat.mem_smoothNumbers_of_lt
      (bankBottomPaperOccurrenceMultiplier_pos _ _)
    exact lt_of_le_of_lt
      (bankBottomPaperOccurrenceMultiplier_le_six _ _)
      (Nat.lt_succ_of_le R.six_le_yNat)
  have hproduct :
      R.ordinary.marker ordinaryRequest *
          R.ordinary.occurrenceCofactor ordinaryRequest ordinaryKind =
        R.bottom.marker bottomRequest *
          bankBottomPaperOccurrenceMultiplier
            (R.bottom.move bottomRequest) bottomKind := by
    calc
      R.ordinary.marker ordinaryRequest *
          R.ordinary.occurrenceCofactor ordinaryRequest ordinaryKind =
          bankBottomPaperOccurrenceMultiplier
              (R.bottom.move bottomRequest) bottomKind *
            R.bottom.marker bottomRequest := by
              simpa only [BankOrdinaryPaperRealization.occurrenceValue,
                BankBottomPaperRealization.occurrenceValue] using heq
      _ = R.bottom.marker bottomRequest *
          bankBottomPaperOccurrenceMultiplier
            (R.bottom.move bottomRequest) bottomKind := Nat.mul_comm _ _
  have hmarkers := primeMarker_mul_smooth_marker_eq
    (R.ordinary.marker_prime ordinaryRequest)
    (R.bottom.marker_prime bottomRequest)
    (R.ordinary.yNat_lt_marker ordinaryRequest)
    (R.bottom.yNat_lt_marker R.ordinary.two_mul_n_le_M
      R.three_mul_yNat_le_n bottomRequest)
    (R.ordinary.occurrenceCofactor_smooth ordinaryRequest ordinaryKind)
    hbottomSmooth hproduct
  exact (ne_of_lt (R.ordinaryMarker_lt_bottomMarker
    ordinaryRequest bottomRequest)) hmarkers

theorem ordinaryComponent_disjoint_bottomComponent
    {n M : ℕ} (R : BankPaperRealization n M)
    (ordinaryRequest : ↑(bankOrdinaryPaperRequests n))
    (bottomRequest : ↑(bankBottomPaperRequests n)) :
    Disjoint (R.ordinary.componentOccurrences ordinaryRequest)
      (R.bottom.componentOccurrences bottomRequest) := by
  rw [Finset.disjoint_left]
  intro occurrence hordinary hbottom
  rw [BankOrdinaryPaperRealization.componentOccurrences,
    Finset.mem_image] at hordinary
  obtain ⟨ordinaryKind, _hkind, hordinaryValue⟩ := hordinary
  have hbottomCarrier :=
    R.bottom.componentOccurrences_subset_carrierValueSet bottomRequest hbottom
  rw [BankBottomPaperRealization.carrierValueSet,
    Finset.mem_image] at hbottomCarrier
  obtain ⟨bottomKind, _hkind, hbottomValue⟩ := hbottomCarrier
  exact (R.ordinaryOccurrence_ne_bottomCarrier ordinaryRequest ordinaryKind
    bottomRequest bottomKind)
      (hordinaryValue.trans hbottomValue.symm)













end BankPaperRealization

/-! ## Terminal combined realization -/



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

/-- Choose the first of `r+1`, `r+2`, `r+3` which avoids both incident
cores. -/
def prefixReplacementCofactor (r left right : ℕ) : ℕ :=
  if r + 1 ≠ left ∧ r + 1 ≠ right then r + 1
  else if r + 2 ≠ left ∧ r + 2 ≠ right then r + 2
  else r + 3



















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralPromotionCostAsymptotic -/
section


/-!
# The residual central-promotion cost

This file proves the quantitative form of (4.10)--(4.11).  The elementary
promotion estimate is summed over the actual residual prime support.  A
Chebyshev estimate then shows that, after choosing one fixed cutoff
parameter, its total cost is an arbitrarily small multiple of `n / log n`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- A real majorant for the total promotion cost at cutoff `X`. -/
def centralPromotionMajorant (n X : ℕ) : ℝ :=
  (Nat.primeCounting X : ℝ) +
    ((Nat.primeCounting X : ℝ) * Real.log (n : ℝ) -
        Chebyshev.theta (X : ℝ)) / Real.log 2





















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



namespace AllocationEntry

/-- Constructor used to keep the literal array compact and readable. -/
def entry (row cofactor numerator denominator : ℕ) : AllocationEntry :=
  ⟨row, cofactor, numerator, denominator⟩

/-- The rational value represented by a certificate entry. -/
def value (e : AllocationEntry) : ℚ :=
  (e.numerator : ℚ) / (max 1 e.denominator : ℕ)

/-- The coordinate occupied by an entry. -/
def coordinate (e : AllocationEntry) : ℕ × ℕ :=
  (e.row, e.cofactor)

end AllocationEntry

open AllocationEntry

/-- The explicit nonzero entries in a single row. -/
def finiteAllocationRowEntries : ℕ → List AllocationEntry
  | 1 => [entry 1 2 4029639598 25970038185, entry 1 3 597400199 51940076370]
  | 2 => [entry 2 3 3432239399 51940076370, entry 2 5 30432359 51940076370]
  | 3 => [entry 3 5 177892183 11130016365, entry 3 7 6149035241 311640458220]
  | 4 => [entry 4 5 1 45]
  | 5 => [entry 5 7 5536939 903305676, entry 5 11 29881539 3312120812]
  | 6 => [entry 6 11 37106416381 5713408400700, entry 6 13 25678291319 5713408400700]
  | 7 => [entry 7 13 1 120]
  | 8 => [entry 8 17 1 153]
  | 9 => [entry 9 13 3520187831 34280450404200, entry 9 17 1970727917 623280916440, entry 9 19 34256599957 17140225202100]
  | 10 => [entry 10 19 1 231]
  | 11 => [entry 11 19 117890228609 51420675606300, entry 11 23 34208283533 25710337803150]
  | 12 => [entry 12 23 1 325]
  | 13 => [entry 13 23 1 378]
  | 14 => [entry 14 29 1 435]
  | 15 => [entry 15 29 1 496]
  | 16 => [entry 16 29 213831204731 174324746984752, entry 16 31 3197967125333 5752716650496816]
  | 17 => [entry 17 31 1 630]
  | 18 => [entry 18 31 142776482538959 143817916262420400, entry 18 37 2286634159870117 5321262901709554800]
  | 19 => [entry 19 31 1 780]
  | 20 => [entry 20 41 1 861]
  | 21 => [entry 21 43 1 946]
  | 22 => [entry 22 41 1 1035]
  | 23 => [entry 23 43 1 1128]
  | 24 => [entry 24 37 10658441105846658564953 17935134484658062065193800, entry 24 43 796497000815658011939 3587026896931612413038760]
  | 25 => [entry 25 31 1 1326]
  | 26 => [entry 26 43 1 1431]
  | 27 => [entry 27 47 1 1540]
  | 28 => [entry 28 53 1 1653]
  | 29 => [entry 29 47 1 1770]
  | 30 => [entry 30 43 1 1891]
  | 31 => [entry 31 61 1 2016]
  | 32 => [entry 32 41 1 2145]
  | 33 => [entry 33 41 1 2278]
  | 34 => [entry 34 61 1 2415]
  | 35 => [entry 35 47 1 2556]
  | 36 => [entry 36 47 1 2701]
  | 37 => [entry 37 41 1 2850]
  | 38 => [entry 38 73 1 3003]
  | 39 => [entry 39 79 1 3160]
  | 40 => [entry 40 43 1 3321]
  | 41 => [entry 41 47 1 3486]
  | 42 => [entry 42 61 1 3655]
  | 43 => [entry 43 47 1 3828]
  | 44 => [entry 44 71 1 4005]
  | 45 => [entry 45 83 1 4186]
  | 46 => [entry 46 73 1 4371]
  | 47 => [entry 47 67 1 4560]
  | 48 => [entry 48 61 1 4753]
  | 49 => [entry 49 53 1 4950]
  | 50 => [entry 50 53 1 5151]
  | 51 => [entry 51 67 1 5356]
  | 52 => [entry 52 59 1 5565]
  | 53 => [entry 53 103 1 5778]
  | 54 => [entry 54 107 1 5995]
  | 55 => [entry 55 103 1 6216]
  | 56 => [entry 56 109 1 6441]
  | 57 => [entry 57 113 1 6670]
  | 58 => [entry 58 79 1 6903]
  | 59 => [entry 59 103 1 7140]
  | 60 => [entry 60 103 1 7381]
  | 61 => [entry 61 107 1 7626]
  | 62 => [entry 62 83 1 7875]
  | 63 => [entry 63 67 1 8128]
  | 64 => [entry 64 83 1 8385]
  | 65 => [entry 65 67 1 8646]
  | 66 => [entry 66 113 1 8911]
  | 67 => [entry 67 83 1 9180]
  | 68 => [entry 68 79 1 9453]
  | 69 => [entry 69 71 1 9730]
  | 70 => [entry 70 73 1 10011]
  | 71 => [entry 71 103 1 10296]
  | 72 => [entry 72 89 1 10585]
  | 73 => [entry 73 103 1 10878]
  | 74 => [entry 74 101 1 11175]
  | 75 => [entry 75 79 1 11476]
  | 76 => [entry 76 101 1 11781]
  | 77 => [entry 77 107 1 12090]
  | 78 => [entry 78 97 1 12403]
  | 79 => [entry 79 83 1 12720]
  | 80 => [entry 80 101 1 13041]
  | 81 => [entry 81 101 1 13366]
  | 82 => [entry 82 103 1 13695]
  | 83 => [entry 83 89 1 14028]
  | 84 => [entry 84 103 1 14365]
  | 85 => [entry 85 101 1 14706]
  | 86 => [entry 86 89 1 15051]
  | 87 => [entry 87 89 1 15400]
  | 88 => [entry 88 101 1 15753]
  | 89 => [entry 89 97 1 16110]
  | 90 => [entry 90 97 1 16471]
  | 91 => [entry 91 97 1 16836]
  | 92 => [entry 92 97 1 17205]
  | 93 => [entry 93 97 1 17578]
  | 94 => [entry 94 97 1 17955]
  | 95 => [entry 95 97 1 18336]
  | 96 => [entry 96 97 1 18721]
  | 97 => [entry 97 191 1 19110]
  | 98 => [entry 98 197 1 19503]
  | 99 => [entry 99 163 1 19900]
  | 100 => [entry 100 191 1 20301]
  | 101 => [entry 101 109 1 20706]
  | 102 => [entry 102 131 1 21115]
  | 103 => [entry 103 199 1 21528]
  | 104 => [entry 104 179 1 21945]
  | 105 => [entry 105 173 1 22366]
  | 106 => [entry 106 199 1 22791]
  | 107 => [entry 107 127 1 23220]
  | 108 => [entry 108 199 1 23653]
  | 109 => [entry 109 151 1 24090]
  | 110 => [entry 110 211 1 24531]
  | 111 => [entry 111 193 1 24976]
  | 112 => [entry 112 193 1 25425]
  | 113 => [entry 113 197 1 25878]
  | 114 => [entry 114 181 1 26335]
  | 115 => [entry 115 167 1 26796]
  | 116 => [entry 116 197 1 27261]
  | 117 => [entry 117 173 1 27730]
  | 118 => [entry 118 193 1 28203]
  | 119 => [entry 119 179 1 28680]
  | 120 => [entry 120 173 1 29161]
  | 121 => [entry 121 163 1 29646]
  | 122 => [entry 122 137 1 30135]
  | 123 => [entry 123 137 1 30628]
  | 124 => [entry 124 167 1 31125]
  | 125 => [entry 125 197 1 31626]
  | 126 => [entry 126 197 1 32131]
  | 127 => [entry 127 157 1 32640]
  | 128 => [entry 128 157 1 33153]
  | 129 => [entry 129 149 1 33670]
  | 130 => [entry 130 131 1 34191]
  | 131 => [entry 131 163 1 34716]
  | 132 => [entry 132 199 1 35245]
  | 133 => [entry 133 211 1 35778]
  | 134 => [entry 134 151 1 36315]
  | 135 => [entry 135 151 1 36856]
  | 136 => [entry 136 149 1 37401]
  | 137 => [entry 137 193 1 37950]
  | 138 => [entry 138 199 1 38503]
  | 139 => [entry 139 197 1 39060]
  | 140 => [entry 140 197 1 39621]
  | 141 => [entry 141 173 1 40186]
  | 142 => [entry 142 149 1 40755]
  | 143 => [entry 143 173 1 41328]
  | 144 => [entry 144 199 1 41905]
  | 145 => [entry 145 167 1 42486]
  | 146 => [entry 146 163 1 43071]
  | 147 => [entry 147 163 1 43660]
  | 148 => [entry 148 173 1 44253]
  | 149 => [entry 149 173 1 44850]
  | 150 => [entry 150 157 1 45451]
  | 151 => [entry 151 163 1 46056]
  | 152 => [entry 152 191 1 46665]
  | 153 => [entry 153 199 1 47278]
  | 154 => [entry 154 193 1 47895]
  | 155 => [entry 155 163 1 48516]
  | 156 => [entry 156 173 1 49141]
  | 157 => [entry 157 197 1 49770]
  | 158 => [entry 158 179 1 50403]
  | 159 => [entry 159 167 1 51040]
  | 160 => [entry 160 181 1 51681]
  | 161 => [entry 161 163 1 52326]
  | 162 => [entry 162 199 1 52975]
  | 163 => [entry 163 193 1 53628]
  | 164 => [entry 164 197 1 54285]
  | 165 => [entry 165 167 1 54946]
  | 166 => [entry 166 181 1 55611]
  | 167 => [entry 167 191 1 56280]
  | 168 => [entry 168 199 1 56953]
  | 169 => [entry 169 173 1 57630]
  | 170 => [entry 170 193 1 58311]
  | 171 => [entry 171 181 1 58996]
  | 172 => [entry 172 193 1 59685]
  | 173 => [entry 173 191 1 60378]
  | 174 => [entry 174 197 1 61075]
  | 175 => [entry 175 179 1 61776]
  | 176 => [entry 176 191 1 62481]
  | 177 => [entry 177 197 1 63190]
  | 178 => [entry 178 191 1 63903]
  | 179 => [entry 179 199 1 64620]
  | 180 => [entry 180 191 1 65341]
  | 181 => [entry 181 197 1 66066]
  | 182 => [entry 182 199 1 66795]
  | 183 => [entry 183 197 1 67528]
  | 184 => [entry 184 197 1 68265]
  | 185 => [entry 185 199 1 69006]
  | 186 => [entry 186 193 1 69751]
  | 187 => [entry 187 193 1 70500]
  | 188 => [entry 188 191 1 71253]
  | 189 => [entry 189 199 1 72010]
  | 190 => [entry 190 197 1 72771]
  | 191 => [entry 191 197 1 73536]
  | 192 => [entry 192 197 1 74305]
  | 193 => [entry 193 199 1 75078]
  | 194 => [entry 194 197 1 75855]
  | 195 => [entry 195 197 1 76636]
  | 196 => [entry 196 199 1 77421]
  | 197 => [entry 197 199 1 78210]
  | 198 => [entry 198 199 1 79003]
  | 199 => [entry 199 347 1 79800]
  | 200 => [entry 200 241 1 80601]
  | _ => []

/-- The twenty-row view of the authoritative row slices. -/
def finiteAllocationRowBlockEntries (b : ℕ) : List AllocationEntry :=
  (List.range' (20 * b + 1) 20).flatMap finiteAllocationRowEntries

/-- The authoritative flat array: the explicit row slices concatenated in
row order. -/
def finiteAllocationEntries : List AllocationEntry :=
  finiteAllocationRowBlockEntries 0 ++ finiteAllocationRowBlockEntries 1 ++
  finiteAllocationRowBlockEntries 2 ++ finiteAllocationRowBlockEntries 3 ++
  finiteAllocationRowBlockEntries 4 ++ finiteAllocationRowBlockEntries 5 ++
  finiteAllocationRowBlockEntries 6 ++ finiteAllocationRowBlockEntries 7 ++
  finiteAllocationRowBlockEntries 8 ++ finiteAllocationRowBlockEntries 9

/-- The cofactor keys occurring in each twenty-row block.  Entry payloads
are not duplicated: prime buckets below filter the authoritative row data. -/
def finiteAllocationPrimeBlockKeys : ℕ → List ℕ
  | 0 => [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
  | 1 => [31, 37, 41, 43, 47, 53, 61, 73, 79]
  | 2 => [47, 53, 59, 61, 67, 71, 73, 79, 83, 103, 107, 109, 113]
  | 3 => [67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 113]
  | 4 => [89, 97, 101, 103, 163, 191, 197]
  | 5 => [109, 127, 131, 151, 167, 173, 179, 181, 193, 197, 199, 211]
  | 6 => [131, 137, 149, 151, 157, 163, 167, 193, 197, 199, 211]
  | 7 => [149, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199]
  | 8 => [163, 167, 173, 179, 181, 191, 193, 197, 199]
  | 9 => [191, 193, 197, 199, 241, 347]
  | _ => []

/-- The entries in one row block having cofactor `p`. -/
def finiteAllocationEntriesForCofactor
    (p : ℕ) (entries : List AllocationEntry) : List AllocationEntry :=
  entries.filter fun e => e.cofactor = p

/-- Within each twenty-row block, a derived regrouping by prime cofactor. -/
def finiteAllocationPrimeBlockBuckets
    (b : ℕ) : List (ℕ × List AllocationEntry) :=
  (finiteAllocationPrimeBlockKeys b).map fun p =>
    (p, finiteAllocationEntriesForCofactor p
      (finiteAllocationRowBlockEntries b))

/-- Select a prime bucket without traversing the entry payloads of rejected
buckets. -/
def selectPrimeEntries (p : ℕ) :
    List (ℕ × List AllocationEntry) → List AllocationEntry
  | [] => []
  | (q, entries) :: buckets =>
      if q = p then entries ++ selectPrimeEntries p buckets
      else selectPrimeEntries p buckets

/-- The twenty explicitly indexed row slices in block `b`. -/
def finiteAllocationRowBlockBuckets (b : ℕ) :
    List (ℕ × List AllocationEntry) :=
  (List.range' (20 * b + 1) 20).map fun r =>
    (r, finiteAllocationRowEntries r)

/-- Selecting row `r` from all ten row blocks. -/
def finiteAllocationSelectedRowEntries (r : ℕ) : List AllocationEntry :=
  selectPrimeEntries r
    ((List.range' 1 200).map fun s => (s, finiteAllocationRowEntries s))

/-- The preaggregated entries contributing to the load at `p`. -/
def finiteAllocationPrimeEntries (p : ℕ) : List AllocationEntry :=
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 0) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 1) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 2) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 3) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 4) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 5) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 6) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 7) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 8) ++
  selectPrimeEntries p (finiteAllocationPrimeBlockBuckets 9)

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







namespace RawFraction

def zero : RawFraction := ⟨0, 1⟩

def add (a b : RawFraction) : RawFraction :=
  ⟨a.numerator * b.denominator + b.numerator * a.denominator,
    a.denominator * b.denominator⟩

def ofEntry (e : AllocationEntry) : RawFraction :=
  ⟨e.numerator, max 1 e.denominator⟩

def toRat (a : RawFraction) : ℚ :=
  (a.numerator : ℚ) / (a.denominator : ℚ)

def sum {α : Type*} (l : List α) (f : α → RawFraction) : RawFraction :=
  match l with
  | [] => zero
  | x :: xs => add (f x) (sum xs f)









end RawFraction

/-- The prime immediately preceding `p` on every range used below. -/
def previousPrime (p : ℕ) : ℕ :=
  Nat.findGreatest Nat.Prime (p - 1)

/-- The finite/tail overlap appearing in the paper's third condition. -/
def finiteTailOverlap (p : ℕ) : ℚ :=
  ∑ r ∈ Finset.Icc (max 201 (previousPrime p)) (p - 1), alpha r

def rawRowMass (r : ℕ) : RawFraction :=
  RawFraction.sum (finiteAllocationRowEntries r) RawFraction.ofEntry

def rawPrimeLoad (p : ℕ) : RawFraction :=
  RawFraction.sum (finiteAllocationPrimeEntries p) RawFraction.ofEntry

def rawAlpha (r : ℕ) : RawFraction :=
  ⟨1, (r + 1) * (2 * r + 1)⟩

def rawCapacity (p : ℕ) : RawFraction :=
  ⟨4029639598, 25970038185 * (p - 1)⟩

def rawTailOverlap (p : ℕ) : RawFraction :=
  let lo := max 201 (previousPrime p)
  RawFraction.sum (List.range' lo ((p - 1) + 1 - lo)) rawAlpha

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificateStructuralChecks -/
section


/-!
# Bounded structural checks for the finite allocation certificate

Every decision here sees at most one twenty-row block, except for the three
linear whole-array audits (length, validity, and primality).
-/

namespace Erdos390.WholePaper

open AllocationEntry

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def allocationKeyLabeled (key : AllocationEntry → ℕ)
    (buckets : List (ℕ × List AllocationEntry)) : Prop :=
  buckets.Forall fun bucket =>
    bucket.2.Forall fun e => key e = bucket.1

def allocationInnerOutputNodup {β : Type*}
    (output : AllocationEntry → β)
    (buckets : List (ℕ × List AllocationEntry)) : Prop :=
  buckets.Forall fun bucket => (bucket.2.map output).Nodup



theorem allocationRowBlockFlat {b : ℕ} (hb : b ≤ 9) :
    finiteAllocationRowBlockEntries b =
      (finiteAllocationRowBlockBuckets b).flatMap fun bucket => bucket.2 := by
  interval_cases b <;> decide



theorem allocationRowLabels {b : ℕ} (hb : b ≤ 9) :
    allocationKeyLabeled (fun e => e.row)
      (finiteAllocationRowBlockBuckets b) := by
  unfold allocationKeyLabeled
  interval_cases b <;> decide



theorem allocationRowCoordinateInnerNodup {b : ℕ} (hb : b ≤ 9) :
    allocationInnerOutputNodup coordinate
      (finiteAllocationRowBlockBuckets b) := by
  unfold allocationInnerOutputNodup finiteAllocationRowBlockBuckets
  interval_cases b <;> decide

 def allocationValidityCheck : Bool :=
  finiteAllocationEntries.all fun e => decide e.Valid

 theorem allocationValidityCheck_eq_true :
    allocationValidityCheck = true := by
  decide

theorem finiteAllocationEntries_valid {e : AllocationEntry}
    (he : e ∈ finiteAllocationEntries) : e.Valid := by
  exact of_decide_eq_true
    ((List.all_eq_true.mp allocationValidityCheck_eq_true) e he)

 def allocationCofactorPrimeCheck : Bool :=
  finiteAllocationEntries.all fun e => decide e.cofactor.Prime





end Erdos390.WholePaper

end


