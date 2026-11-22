-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_headMoments_eq_roundedSource_of_sourceState
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:54:46.029482+00:00
-- url     : https://prove2.me/submissions/4bd8259d-b483-4827-9220-9d5213484c3f

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
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009

/- Source module: Erdos390.Full.PaperCanonicalBaseline -/
section


/-!
# Canonical barycentric baseline allocation

The active bridge first fixes positive head barycentric masses and then mixes
the two separated physical pools to hit the required logarithmic moment.
This file performs that construction exactly on the literal guarded finite
cells.  The resulting common cell-mass margin is an output.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperGuardCensus

open PaperBridgeFit ArithmeticModel

noncomputable section

variable {Head : Type*} [Fintype Head] [Nonempty Head]











namespace BarycentricTarget

variable {D : StructuredSampleData Head} (T : BarycentricTarget D)





























omit [Nonempty Head] in
/-- The two physical signs sum back to the prescribed head barycenter. -/
theorem headMarginal (h : Head) :
    ∑ sigma : PhysicalSign,
        T.baseline.normalizedCellMass (h, sigma) = T.beta h := by
  simp only [T.baseline_normalizedCellMass, cellProbability]
  rw [sum_physicalSign]
  ring

omit [Nonempty Head] in
/-- Hence every prescribed head-linear moment is exact. -/
theorem headMoment (a : Head → ℝ) :
    ∑ c : Cell Head, T.baseline.normalizedCellMass c * a c.1 =
      ∑ h : Head, T.beta h * a h := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h hh
  calc
    ∑ y : PhysicalSign, T.baseline.normalizedCellMass (h, y) * a h =
        (∑ y : PhysicalSign, T.baseline.normalizedCellMass (h, y)) * a h := by
      rw [Finset.sum_mul]
    _ = T.beta h * a h := by rw [T.headMarginal h]



end BarycentricTarget

end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.Full.PaperCanonicalHeadPhysicalTarget -/
section


/-!
# The paper's explicit head simplex and physical interpolation

The head barycenter is not supplied as an arbitrary probability vector in
the paper.  Its nonzero-vertex coefficients are exactly `A_p / (E*q)` and
the zero-vertex coefficient is the remaining mass.  This file constructs
that literal vector from the finite reserve ledger and combines it with the
two fixed physical intervals around `mu`.
-/

open scoped BigOperators

namespace Erdos390.Full

open PaperGuardCensus PaperBridgeFit PaperHeadSimplex ArithmeticModel

noncomputable section

namespace PaperGuardCensus



namespace HeadSimplexReserve

variable {P : Finset ℕ} (R : HeadSimplexReserve P)













theorem exponent_cast_pos : 0 < (R.exponent : ℝ) := by
  exact_mod_cast R.exponent_pos



/-- The displayed barycenter has exactly the normalized target valuation at
each head prime. -/
theorem beta_exponent_moment (p : {p : ℕ // p ∈ P}) :
    ∑ h : PaperHeadSimplex.Tag P,
        R.beta h * (PaperHeadSimplex.exponent P R.exponent h p.1 : ℝ) =
      R.target p / R.activeMass := by
  rw [Fintype.sum_option]
  simp only [beta, PaperHeadSimplex.exponent_none, Nat.cast_zero,
    mul_zero, zero_add]
  rw [Finset.sum_eq_single p]
  · simp only [PaperHeadSimplex.exponent_some_self]
    field_simp [ne_of_gt R.exponent_cast_pos,
      ne_of_gt R.activeMass_pos]
  · intro q hq hqp
    have hval : p.1 ≠ q.1 := by
      intro h
      exact hqp (Subtype.ext h.symm)
    rw [PaperHeadSimplex.exponent_some_ne P R.exponent q p.1 hval]
    simp
  · intro hp
    exact (hp (Finset.mem_univ p)).elim

end HeadSimplexReserve



namespace PhysicalInterpolationTarget

variable {I : PhysicalIntervals}











end PhysicalInterpolationTarget

end PaperGuardCensus

namespace PaperBridgeFit.BridgeData

variable {P : Finset ℕ} {Band : Type*}
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData (PaperHeadSimplex.Tag P) Band)

















end PaperBridgeFit.BridgeData

end

end Erdos390.Full

end

/- Source module: Erdos390.WholePaper.BankPaperProposition87ActualDataConnector -/
section


/-!
# Actual paper data at the Proposition 8.7 / guarded-selector interface

The paper does not use the mass-one normalization of the bridge.  Its
literal active weights are the numbers `z_m^0`, and

`q_n = sum_m z_m^0`.

At a clean numerical coordinate the protected frozen layer may overlap the
active layer.  Consequently `q_n` is not, in general, the sum of the whole
guarded selector on the active support.  This module keeps the two layers
separate.  Every guarded candidate is represented by a frozen tag of weight

`preSelector a - activeSeedAmbient a`,

while Proposition 8.7 evolves the active seed.  Thus the protected overlap
is retained exactly and the combined selector at time zero is the supplied
guarded pre-selector.

The single construction still missing from the finite guarded ledger is
named `BankPaperCanonicalActualActiveMeasureConstructor`.  It asks only for
the paper's active-measure realization: the seed has the canonical
barycentric shape, has eventual paper-scale mass at least one, is supported
on the guarded candidates, and is dominated by the already feasible
pre-selector.  Row integrality, target agreement, band balance, support,
pointwise estimates, and prefix estimates are not repeated in this
constructor; they are derived below from the existing guarded selector and
the Proposition 8.7 path.
-/

open Filter Topology Set
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## The literal active mass and its sole construction socket -/

























/-! ## The actual scaled bridge data -/









/-! ## Tagged frozen remainder and exact push-forward -/





















/-! ## The initial combined selector -/









/-! ## The literal active marked target and endpoint -/













/-! ## Smooth active support and unchanged complete-rough rows -/









/-- The active seed push-forward vanishes at a coordinate which is not the
value of any active sample tag. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (activeSeed : D.Sample -> Real)
    (a : Nat) (ha : forall m : D.Sample, D.value m ≠ a) :
    bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a = 0 := by
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_eq_zero
  intro m _hm
  rw [if_neg (ha m)]













/-! ## Prime support, exact bands, and the derived prefix ledger -/











/-! ## Complete endpoint handoff -/



/-! ## Direct coupling to the guarded continuation -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothAdditivePlacement -/
section


/-!
# Paper-faithful placement boundary for the guarded smooth refinement

The smooth bridge in the paper does not preserve the medium-prime moments
of an earlier provisional selector.  It freezes the protected layer,
redistributes the active mass while preserving the smooth-row ledger and
the moments outside the tangent band, and then fits the medium-prime band
moments.  Proposition 8.7 supplies that latter fit.

Accordingly, the pre-selector part of the actual endpoint theorem needs
only complete-row integrality and deficit support outside the medium-prime
band.  Its older statement accepted a full rounded-selector tangent input,
although the proof used only those two fields.  This file records the
weaker exact theorem, constructs the minimized ledger from the paper's two
literal zero-head cells, and proves the exact scaled structured head-cell
moments.  It then resolves the support boundary--the nonzero head cells lie
in the smooth row, not in its head-free correction subpool--by transporting
a signed ledger over the whole smooth row for the corrected selector.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeSums
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization



/-! ## Exact finite algebra for the two zero-head pools -/





















/-! ## The head-free correction-pool ledger -/











/-! ## Structured head-cell realization -/

/-- Summing a uniform baseline coordinate statistic which depends only on
the structured cell recovers the corresponding cell-mass sum. -/
theorem sum_baselineBaseWeight_mul_cellFunction
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head}
    (A : BaselineAllocation D) (f : Cell Head -> Real) :
    (∑ m : D.Sample, A.baseWeight m * f (D.cellOf m)) =
      ∑ cell : Cell Head, A.cellMass cell * f cell := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro cell _hcell
  simp only [BaselineAllocation.baseWeight, StructuredSampleData.cellOf]
  have hcard : (Fintype.card (D.SampleAt cell) : Real) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (D.sampleAt_card_pos cell)
  change (∑ _ : D.SampleAt cell,
    A.cellMass cell / (Fintype.card (D.SampleAt cell) : ℝ) * f cell) =
      A.cellMass cell * f cell
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]

/-- The canonical scaled seed realizes every prescribed head-tag linear
moment with the literal active-mass factor in front. -/
theorem sum_bankPaperCanonicalScaledActiveSeed_mul_headFunction
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    (q : Real) (phi : Head -> Real) :
    (∑ m : D.Sample,
        bankPaperCanonicalScaledActiveSeed T q m *
          phi (D.cellOf m).1) =
      q * ∑ h : Head, T.beta h * phi h := by
  calc
    (∑ m : D.Sample,
        bankPaperCanonicalScaledActiveSeed T q m *
          phi (D.cellOf m).1) =
      q * ∑ m : D.Sample,
        T.baseline.baseWeight m * phi (D.cellOf m).1 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      unfold bankPaperCanonicalScaledActiveSeed
      ring
    _ = q * ∑ cell : Cell Head,
        T.baseline.cellMass cell * phi cell.1 := by
      apply congrArg (q * ·)
      simpa using
        (sum_baselineBaseWeight_mul_cellFunction
          T.baseline (fun cell => phi cell.1))
    _ = q * ∑ cell : Cell Head,
        T.baseline.normalizedCellMass cell * phi cell.1 := by
      apply congrArg (q * ·)
      apply Finset.sum_congr rfl
      intro cell _hcell
      unfold BaselineAllocation.normalizedCellMass
      rw [T.baseline_totalMass, div_one]
    _ = q * ∑ h : Head, T.beta h * phi h := by
      rw [T.headMoment phi]

/-- Weighted ambient push-forward over a support containing all structured
values is exactly the corresponding tagged weighted sum. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (seed : D.Sample -> Real)
    (support : Finset Nat)
    (hvalues : forall m : D.Sample, D.value m ∈ support)
    (p : Nat) :
    (∑ a ∈ support,
        bankPaperCanonicalActiveSeedAmbientWeight D seed a *
          valuation p a) =
      ∑ m : D.Sample, seed m * valuation p (D.value m) := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_eq_single (D.value m)]
  · simp
  · intro a _ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (hvalues m)).elim

/-- The scaled structured head-simplex seed has exactly the unnormalized
head-prime moment stored in `HeadSimplexReserve`.  This is the finite
coordinate version of the paper's head-cell realization. -/
theorem sum_bankPaperCanonicalScaledActiveSeed_mul_paperHeadValuation
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hprime : ∀ p ∈ P, p.Prime)
    (Rhead : HeadSimplexReserve P)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Kphysical : PhysicalInterpolationTarget I)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime Rhead.exponent)
    (p : {p : Nat // p ∈ P}) :
    let T := B.barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T Rhead.activeMass m *
          valuation p.1 (B.sampleData.value m)) = Rhead.target p := by
  dsimp only
  let T := B.barycentricTargetOfPaperData I hlo hhi Rhead Kphysical
  have hvaluation : forall m : B.sampleData.Sample,
      valuation p.1 (B.sampleData.value m) =
        (PaperHeadSimplex.exponent P Rhead.exponent
          (B.sampleData.cellOf m).1 p.1 : Real) := by
    intro m
    have hpMem : p.1 ∈
        (B.sampleData.pattern (B.sampleData.cellOf m).1).primes := by
      rw [hpattern]
      exact p.2
    have hm := B.sampleData.value_matches_head m p.1 hpMem
    simpa [valuation, hpattern, PaperHeadSimplex.pattern] using
      congrArg (fun k : Nat => (k : Real)) hm
  calc
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T Rhead.activeMass m *
          valuation p.1 (B.sampleData.value m)) =
      ∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T Rhead.activeMass m *
          (PaperHeadSimplex.exponent P Rhead.exponent
            (B.sampleData.cellOf m).1 p.1 : Real) := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [hvaluation m]
    _ = Rhead.activeMass *
        ∑ h : PaperHeadSimplex.Tag P,
          T.beta h *
            (PaperHeadSimplex.exponent P Rhead.exponent h p.1 : Real) :=
      sum_bankPaperCanonicalScaledActiveSeed_mul_headFunction
        T Rhead.activeMass
          (fun h =>
            (PaperHeadSimplex.exponent P Rhead.exponent h p.1 : Real))
    _ = Rhead.activeMass * (Rhead.target p / Rhead.activeMass) := by
      apply congrArg (Rhead.activeMass * ·)
      change (∑ h : PaperHeadSimplex.Tag P,
        Rhead.beta h *
          (PaperHeadSimplex.exponent P Rhead.exponent h p.1 : Real)) = _
      exact Rhead.beta_exponent_moment p
    _ = Rhead.target p := by
      field_simp [ne_of_gt Rhead.activeMass_pos]











/-! ## Exact support boundary -/



/-! ## Signed whole-smooth-row placement ledger -/



































end BankPaperRealization

/-! ## Weaker actual-endpoint preselector interface -/



namespace BankPaperRealization







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightBaselineTargetConnector -/
section


/-!
# The finite post-height baseline target

After the integer height `d` has been selected, the paper chooses a fresh
finite baseline.  Its total active mass is

`q_n = q0 - d`,

its unnormalized head-prime moments are the prescribed values
`A_p^act`, and its normalized logarithmic height above `n` is
`A(d) / q_n`.

In the repository, this last statistic is
`BridgeData.physicalScore = log (m/n)`.  The separately named
`BridgeData.ordinaryLogScore` is `log m`, so its unnormalized moment is
`A(d) + q_n L`, not `A(d)`.  Both identities are proved below.

The two-zero-cell rounding placement used to obtain the integer row quota
need not itself have barycentric product form.  Accordingly this module
does not identify that placement with the new baseline.  It instead uses
the paper's actual `HeadSimplexReserve`, `PhysicalInterpolationTarget`, and
`BridgeData.barycentricTargetOfPaperData` constructors to build a new
`BarycentricTarget`, and proves its finite moment identities directly.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

/-! ## Literal post-height scalar data -/













/-! ## Genuine reserve and interpolation inputs -/



/-! ## Constructed paper data -/









/-! ## Exact mass and head moments -/



/-- At every head prime, the sample-level scaled seed realizes the
unnormalized post-height target `A_p^act` exactly. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_activeSeed_headMoment
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime exponent)
    (p : {p : Nat // p ∈ P}) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m *
          valuation p.1 (B.sampleData.value m)) =
      activeHeadTarget p := by
  simpa only [
    bankPaperCanonicalSectionNinePostHeightActiveSeed,
    bankPaperCanonicalSectionNinePostHeightTarget,
    bankPaperCanonicalSectionNinePostHeightHeadReserve] using
    (BankPaperRealization.sum_bankPaperCanonicalScaledActiveSeed_mul_paperHeadValuation
      B hprime
        (bankPaperCanonicalSectionNinePostHeightHeadReserve H)
        I hlo hhi
        (bankPaperCanonicalSectionNinePostHeightPhysicalTarget H)
        hpattern p)

/-! ## Exact ordinary-log moment -/













/-! ## Combined finite target constructor -/



/-! ## Quantitative target margin -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenSelectorTailSupportReductionConnector -/
section


/-!
# Selector-tail support reduction for the frozen-top sources

Outside the medium-prime band there are two disjoint finite mechanisms.

* At a head prime `q ≤ W`, every raw or constant-pool correction term has
  zero `q`-valuation.  The source moment is therefore exactly the moment of
  the scaled structured seed, hence `Rhead.target`.
* At a high prime `yNat n < q`, factorization is constant on each complete
  rough row.  Charged nonsmooth-row totals, together with postcharge row
  capacity for unattained active rows, identify the source moment with the
  selector-tail target ledger.

Thus the only extra low-prime datum is the literal compatibility

`Rhead.target p =
  (certificate.selectorTailTarget R fixed).factorization p`.

The finite theorems below first expose the low/high reductions separately,
then package selector-tail support for both the literal `qTilde` source and
its nearest-integer rounded counterpart.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Head-prime vanishing -/

/-- A head-compatible raw coordinate has zero weighted valuation at every
prime in the complete head product. -/
theorem
    roughHeadCompatibleRawWeight_mul_factorization_eq_zero_of_headPrime
    {W n h K q a : Nat} {alpha beta ell : Real}
    (hqPrime : q.Prime) (hqW : q <= W) :
    roughHeadCompatibleRawWeight W n h K alpha beta ell a *
        (a.factorization q : Real) = 0 := by
  by_cases hcop : Nat.Coprime a (roughHeadModulus W)
  · have hqHead : q ∈ primesUpTo W :=
      mem_primesUpTo.mpr ⟨hqPrime, hqW⟩
    have hqDvd : q ∣ roughHeadModulus W := by
      unfold roughHeadModulus
      exact Finset.dvd_prod_of_mem (fun r : Nat => r) hqHead
    have haq : Nat.Coprime a q :=
      Nat.Coprime.of_dvd_right hqDvd hcop
    have hfactorization : a.factorization q = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (hqPrime.coprime_iff_not_dvd.mp haq.symm)
    rw [hfactorization]
    ring
  · simp [roughHeadCompatibleRawWeight, hcop]

/-- Every coordinate in any guarded broad correction row—not only the
smooth row—has zero valuation at a head prime. -/
theorem factorization_eq_zero_of_mem_guardedBroadCorrectionPool_of_headPrime_label
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar : Real} {q a : Nat}
    (hqPrime : q.Prime) (hqW : q <= B.sampleData.W)
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K label) :
    a.factorization q = 0 := by
  have haRaw :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
      certificate deltaStar B.sampleData.W K label ha
  have haData := mem_completeRoughRowFiber.mp haRaw
  have haHeadFree := mem_roughHeadFree.mp haData.1
  have hqHead : q ∈ primesUpTo B.sampleData.W :=
    mem_primesUpTo.mpr ⟨hqPrime, hqW⟩
  have hqDvd : q ∣ roughHeadModulus B.sampleData.W := by
    unfold roughHeadModulus
    exact Finset.dvd_prod_of_mem (fun r : Nat => r) hqHead
  have haq : Nat.Coprime a q :=
    Nat.Coprime.of_dvd_right hqDvd haHeadFree.2
  exact Nat.factorization_eq_zero_of_not_dvd
    (hqPrime.coprime_iff_not_dvd.mp haq.symm)

/-- The literal guarded postcharge correction has zero weighted valuation
at every head prime, independently of its row target and density. -/
theorem
    roughCanonicalGuardedPostchargeRowCorrectedWeight_mul_factorization_eq_zero_of_headPrime
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar alpha beta : Real} {q a : Nat}
    (hqPrime : q.Prime) (hqW : q <= B.sampleData.W) :
    R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar B.sampleData.W K label alpha beta B.L a *
        (a.factorization q : Real) = 0 := by
  unfold roughCanonicalGuardedPostchargeRowCorrectedWeight
  unfold bankPaperConstantPoolCorrection
  by_cases haPool :
      a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K label
  · rw [if_pos haPool,
      factorization_eq_zero_of_mem_guardedBroadCorrectionPool_of_headPrime_label
        B R certificate hqPrime hqW haPool]
    ring
  · rw [if_neg haPool]
    simpa using
      (roughHeadCompatibleRawWeight_mul_factorization_eq_zero_of_headPrime
        (W := B.sampleData.W) (n := B.sampleData.n)
        (h := upperTailLength c B.sampleData.n) (K := K)
        (alpha := alpha) (beta := beta) (ell := B.L)
        (q := q) (a := a) hqPrime hqW)

/-- On the guarded candidate set, the complete frozen-top source has the
same head-prime moment pointwise as its ambient structured seed. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_mul_factorization_eq_ambient_of_headPrime
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    {q a : Nat} (hqPrime : q.Prime) (hqW : q <= B.sampleData.W)
    (ha : a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K) :
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a *
        (a.factorization q : Real) =
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed a *
        (a.factorization q : Real) := by
  classical
  by_cases hlabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1
  · have haSmooth :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, hlabel⟩)
    rw [
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
        B R certificate oldSeed haSmooth]
    have hraw :=
      roughHeadCompatibleRawWeight_mul_factorization_eq_zero_of_headPrime
        (W := B.sampleData.W) (n := B.sampleData.n)
        (h := upperTailLength c B.sampleData.n) (K := K)
        (alpha := alpha) (beta := betaProt) (ell := B.L)
        (q := q) (a := a) hqPrime hqW
    calc
      (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a) *
          (a.factorization q : Real) =
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) K alpha betaProt B.L a *
            (a.factorization q : Real) +
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed a *
            (a.factorization q : Real) := by ring
      _ = bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a * (a.factorization q : Real) := by
        rw [hraw]
        ring
  · have hnotSmoothPool :
        a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 := by
      intro haPool
      have haSmooth :
          a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
        R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
          certificate deltaStar B.sampleData.W K 1 haPool
      exact hlabel (mem_completeRoughRowFiber.mp haSmooth).2
    have hambientZero :
        bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      have hmSmooth :=
        hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
      exact hlabel (mem_completeRoughRowFiber.mp hmSmooth).2
    rw [bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
      bankPaperCanonicalTwoZeroHeadCellSourceSelector,
      if_neg hnotSmoothPool,
      bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop,
      if_neg hlabel]
    by_cases hexceptional :
        RoughCanonicalExceptionalLabel B.sampleData.n deltaStar
          (completeRoughLabel (yNat B.sampleData.n) a)
    · rw [if_pos hexceptional, hambientZero]
    · rw [if_neg hexceptional, hambientZero,
        roughCanonicalGuardedPostchargeRowCorrectedWeight_mul_factorization_eq_zero_of_headPrime
          B R certificate hqPrime hqW]
      ring





/-! ## High-prime row reindexing -/











/-! ## WithTop and rounded support wrappers -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourcePrebridgeConnector -/
section


/-!
# The literal frozen-top source-to-post-height prebridge

The frozen-top rounded source contains its own nearest-integer active seed,
whereas the final baseline uses the fresh post-height barycentric seed of
mass `q0-d`.  These seeds are not equal.  What the structured prebridge
needs is instead their exact *signed difference* on the complete smooth
row:

* its total mass is the integer `-d`;
* its valuation moment at every head prime is zero.

This file proves that ledger.  The old head moment is recovered from the
literal source state's zero deficit outside the medium-prime band and the
paper's selector-tail target.  The new head moment is the exact
`activeHeadTarget` realized by the post-height target.  Thus no equality of
the old and new seeds is assumed.

The final theorem combines this ledger with the geometric feasibility
theorem from the post-height placed-measure connector, yielding the actual
measure and the full row-integral structured placement.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

namespace BankPaperRealization

/-! ## The geometric outside compatibility -/



/-! ## Arbitrary replacement of a two-zero-cell source seed -/





/-! ## Recovering the old head moment from the literal source state -/

/-- The source-state support equation at head primes and the exact
post-height target moment identify the old rounded seed moment with the
fresh post-height seed moment.

The only target compatibility is the paper's literal one:
`activeHeadTarget` is the factorization of the selector-tail target at the
corresponding head prime. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_headMoments_eq_roundedSource_of_sourceState
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime exponent)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (htarget : ∀ p : {p : Nat // p ∈ P},
      p.1 ≤ B.sampleData.W →
        activeHeadTarget p =
          ((certificate.selectorTailTarget R
            (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
              Real))
    (Ssource : BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate Tsource deltaStar betaProt
          alpha beta qTilde)) :
    ∀ q : Nat, q.Prime → q ≤ B.sampleData.W →
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H m *
            valuation q (B.sampleData.value m)) =
        ∑ m : B.sampleData.Sample,
          bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate Tsource deltaStar betaProt
                alpha qTilde m *
            valuation q (B.sampleData.value m) := by
  intro q hqPrime hqW
  have hqHead : q ∈ primesUpTo B.sampleData.W :=
    mem_primesUpTo.mpr ⟨hqPrime, hqW⟩
  let p : {p : Nat // p ∈ P} := ⟨q, hhead hqHead⟩
  have hqNotBand : q ∉ primeBand B.sampleData.n B.sampleData.W := by
    intro hqBand
    exact (not_lt_of_ge hqW) (mem_primeBand.mp hqBand).2.1
  have hdeficit :=
    Ssource.deficitSupportedOnPrimeBand q hqPrime hqNotBand
  have hsourceMoment :
      (∑ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K,
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate Tsource deltaStar betaProt
              alpha beta qTilde a *
          (a.factorization q : Real)) =
        ((certificate.selectorTailTarget R
          (R.paperFixedExceptionalFactors deltaStar)).factorization q :
            Real) := by
    unfold bankPaperCanonicalSelectorValuationDeficit at hdeficit
    linarith
  have hsourceAmbient :
      (∑ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K,
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate Tsource deltaStar betaProt
              alpha beta qTilde a *
          (a.factorization q : Real)) =
        ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate Tsource deltaStar betaProt
                  alpha qTilde) a *
            (a.factorization q : Real) := by
    apply Finset.sum_congr rfl
    intro a ha
    simpa only [bankPaperCanonicalTopFrozenRoundedSourceSelector] using
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_mul_factorization_eq_ambient_of_headPrime
        (K := K) B R certificate deltaStar betaProt alpha beta
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate Tsource deltaStar betaProt alpha qTilde)
          hactiveSmooth hqPrime hqW ha)
  have hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
    intro m
    exact
      (mem_completeRoughRowFiber.mp
        (hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr
            ⟨m, rfl⟩))).1
  have hold :
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate Tsource deltaStar betaProt
                alpha qTilde m *
            valuation q (B.sampleData.value m)) =
        ((certificate.selectorTailTarget R
          (R.paperFixedExceptionalFactors deltaStar)).factorization q :
            Real) := by
    calc
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate Tsource deltaStar betaProt
                alpha qTilde m *
            valuation q (B.sampleData.value m)) =
        ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate Tsource deltaStar betaProt
                  alpha qTilde) a *
            valuation q a := by
          symm
          exact
            sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
              B.sampleData
                (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                  B R certificate Tsource deltaStar betaProt
                    alpha qTilde)
                (R.roughCanonicalGuardedCandidateSet
                  certificate deltaStar K)
                hvalues q
      _ =
        ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
              B R certificate Tsource deltaStar betaProt
                alpha beta qTilde a *
            (a.factorization q : Real) := by
          simpa only [valuation] using hsourceAmbient.symm
      _ =
        ((certificate.selectorTailTarget R
          (R.paperFixedExceptionalFactors deltaStar)).factorization q :
            Real) := hsourceMoment
  have hnew :=
    bankPaperCanonicalSectionNinePostHeight_activeSeed_headMoment
      B I hlo hhi H hprime hpattern p
  calc
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m *
          valuation q (B.sampleData.value m)) =
      activeHeadTarget p := by
        simpa only [p] using hnew
    _ =
        ((certificate.selectorTailTarget R
          (R.paperFixedExceptionalFactors deltaStar)).factorization q :
            Real) := by
      simpa only [p] using htarget p hqW
    _ =
        ∑ m : B.sampleData.Sample,
          bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate Tsource deltaStar betaProt
                alpha qTilde m *
            valuation q (B.sampleData.value m) :=
      hold.symm

/-! ## The paper's `q0-d` prebridge ledger -/



/-! ## Row quota and full placement -/





/-! ## One-shot geometric source-to-post-height construction -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

universe u_1
theorem solution :
∀ {P : Finset.{0} Nat} {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band]
  (B :
    @Erdos390.Full.PaperBridgeFit.BridgeData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
      (@instFintypeOption.{0}
        (@Subtype.{1} Nat fun (p : Nat) =>
          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
        (@Finset.Subtype.fintype.{0} Nat P))
      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
        @Option.instDecidableEq.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (fun
              (a b :
                @Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
            @Subtype.instDecidableEq.{1} Nat
              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
              instDecidableEqNat a b)
          a b)
      inst inst_1)
  {c : Real} {depth K : Nat}
  (R :
    Erdos390.WholePaper.BankPaperRealization
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
            @Option.instDecidableEq.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (fun
                  (a b :
                    @Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                @Subtype.instDecidableEq.{1} Nat
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                  instDecidableEqNat a b)
              a b)
          inst inst_1 B))
      (Erdos390.WholePaper.upperEndpoint
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            inst inst_1 B))
        (Erdos390.WholePaper.upperTailLength c
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              inst inst_1 B)))))
  (certificate :
    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
            @Option.instDecidableEq.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (fun
                  (a b :
                    @Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                @Subtype.instDecidableEq.{1} Nat
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                  instDecidableEqNat a b)
              a b)
          inst inst_1 B))
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            inst inst_1 B))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              inst inst_1 B))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                inst inst_1 B))))
        R)
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            inst inst_1 B))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              inst inst_1 B))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                inst inst_1 B))))
        R)
      (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            inst inst_1 B))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              inst inst_1 B))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                inst inst_1 B))))
        R depth))
  (Tsource :
    @Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
      (@instFintypeOption.{0}
        (@Subtype.{1} Nat fun (p : Nat) =>
          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
        (@Finset.Subtype.fintype.{0} Nat P))
      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
          @Option.instDecidableEq.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (fun
                (a b :
                  @Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
              @Subtype.instDecidableEq.{1} Nat
                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                instDecidableEqNat a b)
            a b)
        inst inst_1 B))
  (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals)
  (hlo :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      @Eq.{1} Nat
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            inst inst_1 B)
          sigma)
        (Erdos390.Full.ArithmeticModel.physicalBound (I.lower sigma)
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              inst inst_1 B))))
  (hhi :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      @Eq.{1} Nat
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            inst inst_1 B)
          sigma)
        (Erdos390.Full.ArithmeticModel.physicalBound (I.upper sigma)
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              inst inst_1 B))))
  {q0 A0 : Real} {d : Int} {exponent : Nat}
  {activeHeadTarget :
    (@Subtype.{1} Nat fun (p : Nat) =>
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) →
      Real}
  (H :
    @Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs.{u_1} P Band inst inst_1 B I q0 A0
      d exponent activeHeadTarget)
  (deltaStar betaProt alpha beta qTilde : Real)
  (hprime :
    ∀ (p : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p →
        Nat.Prime p),
  @Eq.{1} (Erdos390.Full.PaperHeadSimplex.Tag P → Erdos390.Full.HeadPattern.Pattern)
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.pattern.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
            @Option.instDecidableEq.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (fun
                  (a b :
                    @Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                @Subtype.instDecidableEq.{1} Nat
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                  instDecidableEqNat a b)
              a b)
          inst inst_1 B))
      (Erdos390.Full.PaperHeadSimplex.pattern P hprime exponent) →
    @HasSubset.Subset.{0} (Finset.{0} Nat) (@Finset.instHasSubset.{0} Nat)
        (@Erdos390.WholePaper.bankPaperCanonicalStructuredActiveValues.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
              @Option.instDecidableEq.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (fun
                    (a b :
                      @Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            inst inst_1 B))
        (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedRow c depth
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                @Option.instDecidableEq.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (fun
                      (a b :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              inst inst_1 B))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                inst inst_1 B)))
          (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                inst inst_1 B))
            (Erdos390.WholePaper.upperEndpoint
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  Band
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  inst inst_1 B))
              (Erdos390.WholePaper.upperTailLength c
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    Band
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                      @Option.instDecidableEq.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (fun
                            (a b :
                              @Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p) =>
                          @Subtype.instDecidableEq.{1} Nat
                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                            instDecidableEqNat a b)
                        a b)
                    inst inst_1 B))))
            R)
          (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                inst inst_1 B))
            (Erdos390.WholePaper.upperEndpoint
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  Band
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  inst inst_1 B))
              (Erdos390.WholePaper.upperTailLength c
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    Band
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                      @Option.instDecidableEq.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (fun
                            (a b :
                              @Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p) =>
                          @Subtype.instDecidableEq.{1} Nat
                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                            instDecidableEqNat a b)
                        a b)
                    inst inst_1 B))))
            R)
          (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                inst inst_1 B))
            (Erdos390.WholePaper.upperEndpoint
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  Band
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  inst inst_1 B))
              (Erdos390.WholePaper.upperTailLength c
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    Band
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                      @Option.instDecidableEq.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (fun
                            (a b :
                              @Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p) =>
                          @Subtype.instDecidableEq.{1} Nat
                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                            instDecidableEqNat a b)
                        a b)
                    inst inst_1 B))))
            R depth)
          R certificate deltaStar K (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      @HasSubset.Subset.{0} (Finset.{0} Nat) (@Finset.instHasSubset.{0} Nat)
          (Erdos390.WholePaper.primesUpTo
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                  @Option.instDecidableEq.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (fun
                        (a b :
                          @Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                inst inst_1 B)))
          P →
        (∀
            (p :
              @Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p),
            @LE.le.{0} Nat instLENat
                (@Subtype.val.{1} Nat
                  (fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  p)
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    Band
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                      @Option.instDecidableEq.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (fun
                            (a b :
                              @Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p) =>
                          @Subtype.instDecidableEq.{1} Nat
                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                            instDecidableEqNat a b)
                        a b)
                    inst inst_1 B)) →
              @Eq.{1} Real (activeHeadTarget p)
                (@Nat.cast.{0} Real Real.instNatCast
                  (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                    Nat (fun (x : Nat) => Nat)
                    (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                    (@Erdos390.WholePaper.GuardedCentralAnchorCertificate.selectorTailTarget c depth
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                              @Option.instDecidableEq.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (fun
                                    (a b :
                                      @Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p) =>
                                  @Subtype.instDecidableEq.{1} Nat
                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P)
                                    instDecidableEqNat a b)
                                a b)
                            inst inst_1 B))
                        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                @Option.instDecidableEq.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (fun
                                      (a b :
                                        @Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p) =>
                                    @Subtype.instDecidableEq.{1} Nat
                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P)
                                      instDecidableEqNat a b)
                                  a b)
                              inst inst_1 B))
                          (Erdos390.WholePaper.upperEndpoint
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (@Finset.Subtype.fintype.{0} Nat P))
                                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                  @Option.instDecidableEq.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (fun
                                        (a b :
                                          @Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p) =>
                                      @Subtype.instDecidableEq.{1} Nat
                                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P)
                                        instDecidableEqNat a b)
                                    a b)
                                inst inst_1 B))
                            (Erdos390.WholePaper.upperTailLength c
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (@Finset.Subtype.fintype.{0} Nat P))
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (@Finset.Subtype.fintype.{0} Nat P))
                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                    @Option.instDecidableEq.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p)
                                      (fun
                                          (a b :
                                            @Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p) =>
                                        @Subtype.instDecidableEq.{1} Nat
                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P)
                                          instDecidableEqNat a b)
                                      a b)
                                  inst inst_1 B))))
                          R)
                        (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                @Option.instDecidableEq.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (fun
                                      (a b :
                                        @Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p) =>
                                    @Subtype.instDecidableEq.{1} Nat
                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P)
                                      instDecidableEqNat a b)
                                  a b)
                              inst inst_1 B))
                          (Erdos390.WholePaper.upperEndpoint
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (@Finset.Subtype.fintype.{0} Nat P))
                                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                  @Option.instDecidableEq.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (fun
                                        (a b :
                                          @Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p) =>
                                      @Subtype.instDecidableEq.{1} Nat
                                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P)
                                        instDecidableEqNat a b)
                                    a b)
                                inst inst_1 B))
                            (Erdos390.WholePaper.upperTailLength c
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (@Finset.Subtype.fintype.{0} Nat P))
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (@Finset.Subtype.fintype.{0} Nat P))
                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                    @Option.instDecidableEq.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p)
                                      (fun
                                          (a b :
                                            @Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p) =>
                                        @Subtype.instDecidableEq.{1} Nat
                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P)
                                          instDecidableEqNat a b)
                                      a b)
                                  inst inst_1 B))))
                          R)
                        (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                @Option.instDecidableEq.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (fun
                                      (a b :
                                        @Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p) =>
                                    @Subtype.instDecidableEq.{1} Nat
                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P)
                                      instDecidableEqNat a b)
                                  a b)
                              inst inst_1 B))
                          (Erdos390.WholePaper.upperEndpoint
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (@Finset.Subtype.fintype.{0} Nat P))
                                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                  @Option.instDecidableEq.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (fun
                                        (a b :
                                          @Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p) =>
                                      @Subtype.instDecidableEq.{1} Nat
                                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P)
                                        instDecidableEqNat a b)
                                    a b)
                                inst inst_1 B))
                            (Erdos390.WholePaper.upperTailLength c
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (@Finset.Subtype.fintype.{0} Nat P))
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (@Finset.Subtype.fintype.{0} Nat P))
                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                    @Option.instDecidableEq.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p)
                                      (fun
                                          (a b :
                                            @Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p) =>
                                        @Subtype.instDecidableEq.{1} Nat
                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P)
                                          instDecidableEqNat a b)
                                      a b)
                                  inst inst_1 B))))
                          R depth)
                        certificate R
                        (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                @Option.instDecidableEq.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (fun
                                      (a b :
                                        @Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p) =>
                                    @Subtype.instDecidableEq.{1} Nat
                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P)
                                      instDecidableEqNat a b)
                                  a b)
                              inst inst_1 B))
                          (Erdos390.WholePaper.upperTailLength c
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (@Finset.Subtype.fintype.{0} Nat P))
                                (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                  @Option.instDecidableEq.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (fun
                                        (a b :
                                          @Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p) =>
                                      @Subtype.instDecidableEq.{1} Nat
                                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P)
                                        instDecidableEqNat a b)
                                    a b)
                                inst inst_1 B)))
                          R deltaStar)).factorization
                    (@Subtype.val.{1} Nat
                      (fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      p)))) →
          @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSelectorSourceState c depth
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  Band
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  inst inst_1 B))
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  Band
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                    @Option.instDecidableEq.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (fun
                          (a b :
                            @Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  inst inst_1 B))
              (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    Band
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                      @Option.instDecidableEq.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (fun
                            (a b :
                              @Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p) =>
                          @Subtype.instDecidableEq.{1} Nat
                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                            instDecidableEqNat a b)
                        a b)
                    inst inst_1 B))
                (Erdos390.WholePaper.upperEndpoint
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      Band
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                        @Option.instDecidableEq.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (fun
                              (a b :
                                @Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
                            @Subtype.instDecidableEq.{1} Nat
                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                              instDecidableEqNat a b)
                          a b)
                      inst inst_1 B))
                  (Erdos390.WholePaper.upperTailLength c
                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                          @Option.instDecidableEq.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (fun
                                (a b :
                                  @Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p) =>
                              @Subtype.instDecidableEq.{1} Nat
                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                                instDecidableEqNat a b)
                            a b)
                        inst inst_1 B))))
                R)
              (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    Band
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                      @Option.instDecidableEq.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (fun
                            (a b :
                              @Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p) =>
                          @Subtype.instDecidableEq.{1} Nat
                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                            instDecidableEqNat a b)
                        a b)
                    inst inst_1 B))
                (Erdos390.WholePaper.upperEndpoint
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      Band
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                        @Option.instDecidableEq.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (fun
                              (a b :
                                @Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
                            @Subtype.instDecidableEq.{1} Nat
                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                              instDecidableEqNat a b)
                          a b)
                      inst inst_1 B))
                  (Erdos390.WholePaper.upperTailLength c
                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                          @Option.instDecidableEq.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (fun
                                (a b :
                                  @Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p) =>
                              @Subtype.instDecidableEq.{1} Nat
                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                                instDecidableEqNat a b)
                            a b)
                        inst inst_1 B))))
                R)
              (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    Band
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                      @Option.instDecidableEq.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (fun
                            (a b :
                              @Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p) =>
                          @Subtype.instDecidableEq.{1} Nat
                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                            instDecidableEqNat a b)
                        a b)
                    inst inst_1 B))
                (Erdos390.WholePaper.upperEndpoint
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      Band
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                        @Option.instDecidableEq.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (fun
                              (a b :
                                @Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
                            @Subtype.instDecidableEq.{1} Nat
                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                              instDecidableEqNat a b)
                          a b)
                      inst inst_1 B))
                  (Erdos390.WholePaper.upperTailLength c
                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                          @Option.instDecidableEq.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (fun
                                (a b :
                                  @Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p) =>
                              @Subtype.instDecidableEq.{1} Nat
                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                                instDecidableEqNat a b)
                            a b)
                        inst inst_1 B))))
                R depth)
              R certificate
              (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    Band
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                      @Option.instDecidableEq.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (fun
                            (a b :
                              @Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p) =>
                          @Subtype.instDecidableEq.{1} Nat
                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                            instDecidableEqNat a b)
                        a b)
                    inst inst_1 B))
                (Erdos390.WholePaper.upperTailLength c
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      Band
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                        @Option.instDecidableEq.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (fun
                              (a b :
                                @Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
                            @Subtype.instDecidableEq.{1} Nat
                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                              instDecidableEqNat a b)
                          a b)
                      inst inst_1 B)))
                R deltaStar)
              (@Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet c depth
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    Band
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                      @Option.instDecidableEq.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (fun
                            (a b :
                              @Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p) =>
                          @Subtype.instDecidableEq.{1} Nat
                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                            instDecidableEqNat a b)
                        a b)
                    inst inst_1 B))
                (Erdos390.WholePaper.upperTailLength c
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      Band
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                        @Option.instDecidableEq.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (fun
                              (a b :
                                @Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
                            @Subtype.instDecidableEq.{1} Nat
                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                              instDecidableEqNat a b)
                          a b)
                      inst inst_1 B)))
                (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      Band
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                        @Option.instDecidableEq.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (fun
                              (a b :
                                @Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
                            @Subtype.instDecidableEq.{1} Nat
                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                              instDecidableEqNat a b)
                          a b)
                      inst inst_1 B))
                  (Erdos390.WholePaper.upperEndpoint
                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                          @Option.instDecidableEq.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (fun
                                (a b :
                                  @Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p) =>
                              @Subtype.instDecidableEq.{1} Nat
                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                                instDecidableEqNat a b)
                            a b)
                        inst inst_1 B))
                    (Erdos390.WholePaper.upperTailLength c
                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                          (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                            @Option.instDecidableEq.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (fun
                                  (a b :
                                    @Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p) =>
                                @Subtype.instDecidableEq.{1} Nat
                                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P)
                                  instDecidableEqNat a b)
                              a b)
                          inst inst_1 B))))
                  R)
                (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      Band
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                        @Option.instDecidableEq.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (fun
                              (a b :
                                @Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
                            @Subtype.instDecidableEq.{1} Nat
                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                              instDecidableEqNat a b)
                          a b)
                      inst inst_1 B))
                  (Erdos390.WholePaper.upperEndpoint
                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                          @Option.instDecidableEq.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (fun
                                (a b :
                                  @Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p) =>
                              @Subtype.instDecidableEq.{1} Nat
                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                                instDecidableEqNat a b)
                            a b)
                        inst inst_1 B))
                    (Erdos390.WholePaper.upperTailLength c
                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                          (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                            @Option.instDecidableEq.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (fun
                                  (a b :
                                    @Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p) =>
                                @Subtype.instDecidableEq.{1} Nat
                                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P)
                                  instDecidableEqNat a b)
                              a b)
                          inst inst_1 B))))
                  R)
                (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@instFintypeOption.{0}
                      (@Subtype.{1} Nat fun (p : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                      (@Finset.Subtype.fintype.{0} Nat P))
                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      Band
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                        @Option.instDecidableEq.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (fun
                              (a b :
                                @Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
                            @Subtype.instDecidableEq.{1} Nat
                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                              instDecidableEqNat a b)
                          a b)
                      inst inst_1 B))
                  (Erdos390.WholePaper.upperEndpoint
                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                          @Option.instDecidableEq.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (fun
                                (a b :
                                  @Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p) =>
                              @Subtype.instDecidableEq.{1} Nat
                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                                instDecidableEqNat a b)
                            a b)
                        inst inst_1 B))
                    (Erdos390.WholePaper.upperTailLength c
                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                          (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                            @Option.instDecidableEq.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (fun
                                  (a b :
                                    @Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p) =>
                                @Subtype.instDecidableEq.{1} Nat
                                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P)
                                  instDecidableEqNat a b)
                              a b)
                          inst inst_1 B))))
                  R depth)
                R certificate deltaStar K)
              (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenRoundedSourceSelector.{u_1} P Band
                inst inst_1 B c depth K R certificate Tsource deltaStar betaProt alpha beta qTilde) →
            ∀ (q : Nat),
              Nat.Prime q →
                @LE.le.{0} Nat instLENat q
                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                      (@instFintypeOption.{0}
                        (@Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                        (@Finset.Subtype.fintype.{0} Nat P))
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                          @Option.instDecidableEq.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (fun
                                (a b :
                                  @Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p) =>
                              @Subtype.instDecidableEq.{1} Nat
                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                                instDecidableEqNat a b)
                            a b)
                        inst inst_1 B)) →
                  @Eq.{1} Real
                    (@Finset.sum.{0, 0}
                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0}
                        (Erdos390.Full.PaperHeadSimplex.Tag P)
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                          (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                            @Option.instDecidableEq.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (fun
                                  (a b :
                                    @Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p) =>
                                @Subtype.instDecidableEq.{1} Nat
                                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P)
                                  instDecidableEqNat a b)
                              a b)
                          inst inst_1 B))
                      Real Real.instAddCommMonoid
                      (@Finset.univ.{0}
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0}
                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                              @Option.instDecidableEq.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (fun
                                    (a b :
                                      @Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p) =>
                                  @Subtype.instDecidableEq.{1} Nat
                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P)
                                    instDecidableEqNat a b)
                                a b)
                            inst inst_1 B))
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{0}
                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                              @Option.instDecidableEq.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (fun
                                    (a b :
                                      @Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p) =>
                                  @Subtype.instDecidableEq.{1} Nat
                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P)
                                    instDecidableEqNat a b)
                                a b)
                            inst inst_1 B)))
                      fun
                        (m :
                          @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0}
                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                @Option.instDecidableEq.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (fun
                                      (a b :
                                        @Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p) =>
                                    @Subtype.instDecidableEq.{1} Nat
                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P)
                                      instDecidableEqNat a b)
                                  a b)
                              inst inst_1 B)) =>
                      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightActiveSeed.{u_1} P Band inst inst_1
                          B I hlo hhi q0 A0 d exponent activeHeadTarget H m)
                        (Erdos390.Full.ArithmeticModel.valuation q
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{0}
                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                @Option.instDecidableEq.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (fun
                                      (a b :
                                        @Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p) =>
                                    @Subtype.instDecidableEq.{1} Nat
                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P)
                                      instDecidableEqNat a b)
                                  a b)
                              inst inst_1 B)
                            m)))
                    (@Finset.sum.{0, 0}
                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0}
                        (Erdos390.Full.PaperHeadSimplex.Tag P)
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                          (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                            @Option.instDecidableEq.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (fun
                                  (a b :
                                    @Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p) =>
                                @Subtype.instDecidableEq.{1} Nat
                                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P)
                                  instDecidableEqNat a b)
                              a b)
                          inst inst_1 B))
                      Real Real.instAddCommMonoid
                      (@Finset.univ.{0}
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0}
                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                              @Option.instDecidableEq.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (fun
                                    (a b :
                                      @Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p) =>
                                  @Subtype.instDecidableEq.{1} Nat
                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P)
                                    instDecidableEqNat a b)
                                a b)
                            inst inst_1 B))
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{0}
                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                              @Option.instDecidableEq.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (fun
                                    (a b :
                                      @Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p) =>
                                  @Subtype.instDecidableEq.{1} Nat
                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P)
                                    instDecidableEqNat a b)
                                a b)
                            inst inst_1 B)))
                      fun
                        (m :
                          @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0}
                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                @Option.instDecidableEq.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (fun
                                      (a b :
                                        @Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p) =>
                                    @Subtype.instDecidableEq.{1} Nat
                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P)
                                      instDecidableEqNat a b)
                                  a b)
                              inst inst_1 B)) =>
                      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenRoundedActiveSeed.{u_1} P
                          Band inst inst_1 B c depth K R certificate Tsource deltaStar betaProt alpha qTilde m)
                        (Erdos390.Full.ArithmeticModel.valuation q
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{0}
                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                @Option.instDecidableEq.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (fun
                                      (a b :
                                        @Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p) =>
                                    @Subtype.instDecidableEq.{1} Nat
                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P)
                                      instDecidableEqNat a b)
                                  a b)
                              inst inst_1 B)
                            m))) := by
  exact @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_headMoments_eq_roundedSource_of_sourceState
