-- Prove2me | solution 1 for Erdos390.WholePaper.bankPaperCanonical_logCurrentLower_mul_portNumerator_le_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:17:03.194006+00:00
-- url     : https://prove2.me/submissions/a674abba-eec4-4a5e-a195-b05ee94eedfb

import Definitions.Def_erdos390_analytic_compact_goals_002
import Definitions.Def_erdos390_analytic_statement_auxiliaries
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_010

/- Source module: Erdos390.Full.PrimeBandQuadrature -/
section


/-!
# Audited harmonic prime quadrature on moving positive cells

The continuum transfer in Lemma 8.4 uses prime cells whose endpoints are
powers of the smoothness scale.  This file starts the required arithmetic
quadrature from the actual Chebyshev function.  The key identity below has no
Mertens constant: it subtracts Abel summation at two endpoints and isolates
the quantitative PNT remainder exactly.
-/

open scoped BigOperators
open Set
open Filter Topology Asymptotics

noncomputable section

namespace Erdos390.Full.PrimeBandQuadrature

open MeasureTheory
open Erdos390.Full.PrimeSums
open Erdos390.Full.FriableAsymptotic



























/-! ## The first logarithmic moment -/















/-! ## Quantitative PNT remainder -/





















/-! ## Exact alignment with the paper's logarithmic coordinate -/





















theorem fullReciprocalSumUniformConstant_pos :
    0 < fullReciprocalSumUniformConstant :=
  (Classical.choose_spec
    exists_fullReciprocalSum_interval_error_bound).1



theorem fullReciprocalSumUniform_bound
    (A Y : ℕ) (hA : fullReciprocalSumUniformCutoff ≤ A)
    (hAY : A ≤ Y) :
    |fullReciprocalSum Y - fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
      5 * fullReciprocalSumUniformConstant / Real.log (A : ℝ) ^ 3 :=
  (Classical.choose_spec
    (Classical.choose_spec
      exists_fullReciprocalSum_interval_error_bound).2) A Y hA hAY



end Erdos390.Full.PrimeBandQuadrature

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTangentResidualBridge -/
section


/-!
# Literal canonical residual for the selector-to-tangent handoff

The canonical Saias reduction currently stops at a selector continuation: it
does not yet construct the pre-tangent rounded selector.  This file removes
the *generic residual* ambiguity without asserting that missing construction.

For a supplied selector `x`, the residual coordinate at a medium prime is
defined literally as

`valuation(selectorTailTarget) - valuation(x)`.

The two remaining selector inputs are named explicitly.  The post-rounding
prime-band balance says that these coordinates sum to zero, while prime-band
support says that the selector already has the target valuation at every
prime outside the band.  Neither fact follows merely from
`roughCanonicalRawRowQuotaError`: that quantity is a complete-rough row quota
error, not a prime-coordinate valuation identity.

From those inputs, the finite prime residual has zero total mass and its
positive star split requests have exactly the valuation deficit required by
`tangentUpdate_valuation_eq_target`.  The final theorem also retains the
all-row integrality input verbatim.  It does not claim that clean common
multipliers, feasibility of the tangent update, or the selector itself have
already been constructed.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Literal selector deficit and its finite prime domain -/















/-! ## Prime-label geometry and exact residual algebra -/

/-- The subtype-to-natural prime label map is injective. -/
theorem bankPaperCanonicalTangentPrimeLabel_injective
    {n W : ℕ} :
    Function.Injective
      (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W)) := by
  intro p q hpq
  exact Subtype.ext hpq

/-- Every canonical tangent label is prime. -/
theorem bankPaperCanonicalTangentPrimeLabel_prime
    {n W : ℕ} (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p).Prime := by
  exact prime_of_mem_primeBand p.2











/-! ## Instantiation of the star split-request boundary -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalPrefixQuadrature -/
section


/-!
# Harmonic-prime majorants for the canonical prefix adapter

The prefix adapter reduces a signed ratio-cell prefix to the strict tail of
the declared pointwise residual bound.  In the paper that bound is a fixed
nonnegative scale times `1 / p`.  This file performs the remaining analytic
step from literal finite tails to the verified uniform Mertens estimate.

No distribution assertion about the ratio cells is built into the result.
The only geometric input says that every prime in a declared strict tail
lies in an explicit numerical interval `(A,Y]`.  The tail can be an arbitrary
subset of that interval; positivity then permits comparison with the full
prime harmonic sum.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature

noncomputable section







-- `WholePaper` also has a distinct presentation of `primesUpTo`; the
-- qualification here keeps this set definitionally aligned with
-- `Full.PrimeSums.fullReciprocalSum`.
private theorem bankPaperCanonical_primesUpTo_mono
    {A Y : Nat} (hAY : A <= Y) :
    Erdos390.Full.PrimeSums.primesUpTo A ⊆
      Erdos390.Full.PrimeSums.primesUpTo Y := by
  intro p hp
  simp only [Erdos390.Full.PrimeSums.primesUpTo,
    Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hAY⟩, hp.2⟩

private theorem bankPaperCanonical_reciprocalPrimeInterval_eq_sub
    {A Y : Nat} (hAY : A <= Y) :
    (∑ p ∈ Erdos390.Full.PrimeSums.primesUpTo Y \
        Erdos390.Full.PrimeSums.primesUpTo A, 1 / (p : Real)) =
      fullReciprocalSum Y - fullReciprocalSum A := by
  have hsub := bankPaperCanonical_primesUpTo_mono hAY
  have hsum := Finset.sum_sdiff hsub
    (f := fun p : Nat => 1 / (p : Real))
  unfold fullReciprocalSum
  exact (eq_sub_iff_add_eq).2 hsum

/-- An arbitrary strict ratio-cell tail with pointwise bound `scale / p` is
bounded by the full harmonic prime mass of any numerical interval containing
that tail.

The interval condition is deliberately one-sided: it does not assert that
the ratio-cell tail contains every prime in `(A,Y]`. -/
theorem tangentRatioCellTail_harmonicPointwiseUpper_le_fullReciprocalSum_sub
    {n W : Nat} {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (scale : Real) (hscale : 0 <= scale)
    (band : Band) (cut A Y : Nat) (hAY : A <= Y)
    (hgeometry : forall p : BankPaperCanonicalTangentPrime n W,
      bandOf p = band -> cut < cellIndex p ->
        A < bankPaperCanonicalTangentPrimeLabel p ∧
          bankPaperCanonicalTangentPrimeLabel p <= Y) :
    tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        bandOf cellIndex band cut <=
      scale * (fullReciprocalSum Y - fullReciprocalSum A) := by
  let tail : Finset (BankPaperCanonicalTangentPrime n W) :=
    Finset.univ.filter
      (fun p => bandOf p = band ∧ cut < cellIndex p)
  let labelEmbedding : BankPaperCanonicalTangentPrime n W ↪ Nat :=
    ⟨bankPaperCanonicalTangentPrimeLabel,
      bankPaperCanonicalTangentPrimeLabel_injective⟩
  let labels : Finset Nat := tail.map labelEmbedding
  have hlabels : labels ⊆
      Erdos390.Full.PrimeSums.primesUpTo Y \
        Erdos390.Full.PrimeSums.primesUpTo A := by
    intro q hq
    have hq' : q ∈ tail.map labelEmbedding := by
      simpa only [labels] using hq
    obtain ⟨p, hpTail, hpq⟩ := Finset.mem_map.mp hq'
    subst q
    have hpCondition : bandOf p = band ∧ cut < cellIndex p :=
      (Finset.mem_filter.mp hpTail).2
    have hpInterval := hgeometry p hpCondition.1 hpCondition.2
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · simp only [Erdos390.Full.PrimeSums.primesUpTo,
        Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.zero_le _, hpInterval.2⟩,
        bankPaperCanonicalTangentPrimeLabel_prime p⟩
    · intro hpA
      simp only [Erdos390.Full.PrimeSums.primesUpTo,
        Finset.mem_filter, Finset.mem_Icc] at hpA
      exact (Nat.not_lt_of_ge hpA.1.2) hpInterval.1
  have htail :
      tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalHarmonicPointwiseUpper scale)
          bandOf cellIndex band cut =
        ∑ p ∈ tail,
          scale / (bankPaperCanonicalTangentPrimeLabel p : Real) := by
    simp only [tangentRatioCellTailPointwiseUpper,
      bankPaperCanonicalHarmonicPointwiseUpper, tail, Finset.sum_filter]
  have hmap :
      (∑ p ∈ tail,
          scale / (bankPaperCanonicalTangentPrimeLabel p : Real)) =
        ∑ q ∈ labels, scale / (q : Real) := by
    simp only [labels, Finset.sum_map]
    rfl
  have hsum :
      (∑ q ∈ labels, scale / (q : Real)) <=
        ∑ q ∈ Erdos390.Full.PrimeSums.primesUpTo Y \
            Erdos390.Full.PrimeSums.primesUpTo A,
          scale / (q : Real) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hlabels
      (fun q _hq _hnot => div_nonneg hscale (Nat.cast_nonneg q))
  calc
    tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        bandOf cellIndex band cut =
      ∑ p ∈ tail,
        scale / (bankPaperCanonicalTangentPrimeLabel p : Real) := htail
    _ = ∑ q ∈ labels, scale / (q : Real) := hmap
    _ <= ∑ q ∈ Erdos390.Full.PrimeSums.primesUpTo Y \
          Erdos390.Full.PrimeSums.primesUpTo A,
        scale / (q : Real) := hsum
    _ = scale *
        (∑ q ∈ Erdos390.Full.PrimeSums.primesUpTo Y \
            Erdos390.Full.PrimeSums.primesUpTo A,
          1 / (q : Real)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      ring
    _ = scale * (fullReciprocalSum Y - fullReciprocalSum A) := by
      rw [bankPaperCanonical_reciprocalPrimeInterval_eq_sub hAY]

/-- Uniform log-log majorant for a literal canonical strict tail.  The same
global constant and cutoff work for every band, cut, and moving endpoint
pair satisfying the displayed geometry. -/
theorem tangentRatioCellTail_harmonicPointwiseUpper_le_uniformMajorant
    {n W : Nat} {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (scale : Real) (hscale : 0 <= scale)
    (band : Band) (cut A Y : Nat)
    (hA : fullReciprocalSumUniformCutoff <= A) (hAY : A <= Y)
    (hgeometry : forall p : BankPaperCanonicalTangentPrime n W,
      bandOf p = band -> cut < cellIndex p ->
        A < bankPaperCanonicalTangentPrimeLabel p ∧
          bankPaperCanonicalTangentPrimeLabel p <= Y) :
    tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        bandOf cellIndex band cut <=
      bankPaperCanonicalHarmonicTailMajorant scale A Y := by
  have hquadrature := fullReciprocalSumUniform_bound A Y hA hAY
  have hupper :
      fullReciprocalSum Y - fullReciprocalSum A <=
        Real.log (Real.log (Y : Real)) -
            Real.log (Real.log (A : Real)) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 3 := by
    have hdeviation :
        fullReciprocalSum Y - fullReciprocalSum A -
            (Real.log (Real.log (Y : Real)) -
              Real.log (Real.log (A : Real))) <=
          |fullReciprocalSum Y - fullReciprocalSum A -
            (Real.log (Real.log (Y : Real)) -
              Real.log (Real.log (A : Real)))| :=
      le_abs_self _
    linarith
  calc
    tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        bandOf cellIndex band cut <=
      scale * (fullReciprocalSum Y - fullReciprocalSum A) :=
        tangentRatioCellTail_harmonicPointwiseUpper_le_fullReciprocalSum_sub
          bandOf cellIndex scale hscale band cut A Y hAY hgeometry
    _ <= scale *
        (Real.log (Real.log (Y : Real)) -
            Real.log (Real.log (A : Real)) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 3) :=
      mul_le_mul_of_nonneg_left hupper hscale
    _ = bankPaperCanonicalHarmonicTailMajorant scale A Y := rfl



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRatioCellGeometry -/
section


/-!
# Canonical exponent bands and merged multiplicative ratio cells

This file supplies the elementary geometry missing between the canonical
regular exponent mesh and the explicit ratio-cell earthmover.

For a natural lower endpoint `A` and a fixed real `rho > 1`, the raw
multiplicative cutoffs are

`floor (A * rho ^ k)`.

The raw cell of a label is the first interval

`(floor (A * rho ^ k), floor (A * rho ^ (k+1))]`

which contains it.  In each canonical exponent band the final raw fragment
is merged into its predecessor.  Thus a merged cell contains at most two raw
cells, and adjacent merged cells span at most three powers of `rho`.  This is
the exact reason that the paper chooses `rho ^ 3 < r0`.

Everything in this module is finite and elementary.  The final section
isolates the one genuinely analytic input still needed for the earthmover:
prime occupancy of every full fixed-ratio interval.  No prime-distribution
statement is stored in the geometry construction.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.PositiveCellTransfer
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## Raw multiplicative cells -/





theorem tangentMultiplicativeRatioCutoff_mono
    {lower : Nat} {rho : Real} (hrho : 1 <= rho) :
    Monotone (tangentMultiplicativeRatioCutoff lower rho) := by
  intro i j hij
  unfold tangentMultiplicativeRatioCutoff
  apply Nat.floor_mono
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_right₀ (by linarith) hij
  · exact Nat.cast_nonneg lower







theorem tangentMultiplicativeRatioCutoff_rawCell_lt_label
    {lower label : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) (hlabel : lower < label) :
    tangentMultiplicativeRatioCutoff lower rho
        (tangentMultiplicativeRawCellIndex lower label rho) < label := by
  let H := exists_label_le_tangentMultiplicativeRatioCutoff_succ
    hlower hrho label
  unfold tangentMultiplicativeRawCellIndex
  rw [dif_pos ⟨hlower, hrho⟩]
  by_cases hk : Nat.find H = 0
  · simpa only [hk, tangentMultiplicativeRatioCutoff_zero] using hlabel
  · have hkone : 1 <= Nat.find H := Nat.one_le_iff_ne_zero.mpr hk
    have hminimal := Nat.find_min H
      (m := Nat.find H - 1) (Nat.sub_one_lt hk)
    have hpred : Nat.find H - 1 + 1 = Nat.find H :=
      Nat.sub_add_cancel hkone
    rw [hpred] at hminimal
    exact Nat.lt_of_not_ge hminimal









/-! ## Merging the terminal fragment -/







theorem tangentMergedRatioCellIndex_le_raw
    (lastRaw raw : Nat) :
    tangentMergedRatioCellIndex lastRaw raw <= raw := by
  exact Nat.min_le_left _ _













/-! ## The canonical paper exponent bands -/









theorem bankPaperCanonicalExponentBandOf_mem_interval
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalExponentBandLower M n W
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) < p.1 ∧
      p.1 <= bankPaperCanonicalExponentBandUpper M n W
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) := by
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S
  let E := RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
    M hdelta hn hW S
  have hp := (E.band_eq_iff p (P.band p)).mp rfl
  simpa only [P, E, bankPaperCanonicalExponentBandOf,
    bankPaperCanonicalExponentBandLower,
    bankPaperCanonicalExponentBandUpper,
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower,
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_upper] using hp

theorem bankPaperCanonicalExponentBandLower_pos
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (band : BankPaperCanonicalExponentBand M) :
    0 < bankPaperCanonicalExponentBandLower M n W band := by
  have hcut :=
    (RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
      M hdelta hn hW S).cutoff_le_lower band
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW
  simpa only [bankPaperCanonicalExponentBandLower,
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower] using
      hWpos.trans_le hcut



















/-! ## Exact analytic occupancy boundary -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRatioCellTraffic -/
section


/-!
# Analytic envelopes for the canonical ratio cells

This file is the first analytic layer after the concrete ratio-cell
geometry.  It makes three facts explicit.

* A strict tail after cell `cut` lies between the next multiplicative
  cutoff and the upper endpoint of its canonical exponent band.  Capping
  the lower endpoint by the band upper endpoint makes the statement valid
  for every natural `cut`, including vacuous cuts beyond the last cell.
* Every full raw interval contained in a merged cell injects into the
  actual finite cell.  The fixed-ratio PNT therefore gives a quantitative
  lower bound for the literal denominator used by the distributed port.
* Uniform Mertens and the PNT denominator combine into finite cut-traffic
  and pointwise-port envelopes.  No mesh sum is estimated here: the final
  Riemann-sum collapse is deliberately left as a separate analytic step.

There are no new distribution hypotheses.  The only asymptotic inputs are
the audited safe PNT and uniform reciprocal-prime estimate already present
in the repository.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## Concrete endpoints for strict cell tails -/





theorem bankPaperCanonicalRatioCellTailLower_le_upper
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho : Real)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) :
    bankPaperCanonicalRatioCellTailLower M n W rho band cut <=
      bankPaperCanonicalRatioCellTailUpper M n W band := by
  exact Nat.min_le_right _ _

/-- The fixed cutoff lies below every canonical exponent-band lower
endpoint. -/
theorem bankPaperCanonical_fixedCutoff_le_exponentBandLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (band : BankPaperCanonicalExponentBand M) :
    W <= bankPaperCanonicalExponentBandLower M n W band := by
  have hcut :=
    (RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
      M hdelta hn hW S).cutoff_le_lower band
  simpa only [bankPaperCanonicalExponentBandLower,
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower] using hcut

/-- Both branches in the capped lower endpoint remain above the fixed
cutoff. -/
theorem bankPaperCanonical_fixedCutoff_le_ratioCellTailLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) :
    W <= bankPaperCanonicalRatioCellTailLower M n W rho band cut := by
  have hWLower := bankPaperCanonical_fixedCutoff_le_exponentBandLower
    M hdelta hn hW S band
  have hcutMono := tangentMultiplicativeRatioCutoff_mono
    (lower := bankPaperCanonicalExponentBandLower M n W band)
    (rho := rho) hrho.le
  have hWNext : W <= tangentMultiplicativeRatioCutoff
      (bankPaperCanonicalExponentBandLower M n W band) rho (cut + 1) := by
    exact hWLower.trans (by
      simpa only [tangentMultiplicativeRatioCutoff_zero] using
        hcutMono (Nat.zero_le (cut + 1)))
  have hWUpper : W <= bankPaperCanonicalExponentBandUpper M n W band := by
    obtain ⟨p, hp⟩ :=
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn hW S).fiber_nonempty band
    have hpInterval :=
      ((RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
        M hdelta hn hW S).band_eq_iff p band).mp hp
    exact hWLower.trans (hpInterval.1.le.trans hpInterval.2)
  exact le_min hWNext hWUpper

/-- Every prime in a declared strict merged-cell tail lies in the concrete
numerical interval used by the Mertens estimate. -/
theorem bankPaperCanonical_ratioCellTail_mem_interval
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat)
    (p : BankPaperCanonicalTangentPrime n W)
    (hpBand : bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band)
    (hpCut : cut <
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p) :
    bankPaperCanonicalRatioCellTailLower M n W rho band cut <
        bankPaperCanonicalTangentPrimeLabel p ∧
      bankPaperCanonicalTangentPrimeLabel p <=
        bankPaperCanonicalRatioCellTailUpper M n W band := by
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let raw := bankPaperCanonicalRawRatioCellIndex
    M hdelta hn hW S rho p
  have hlower : 0 < lower := by
    exact bankPaperCanonicalExponentBandLower_pos
      M hdelta hn hW S band
  have hpLower : lower < p.1 := by
    have hp :=
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S p).1
    simpa only [lower, hpBand] using hp
  have hpUpper : p.1 <= bankPaperCanonicalExponentBandUpper M n W band := by
    have hp :=
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S p).2
    simpa only [hpBand] using hp
  have hmergedLeRaw :
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p <= raw := by
    unfold bankPaperCanonicalRatioCellIndex
    exact tangentMergedRatioCellIndex_le_raw _ _
  have hcutRaw : cut + 1 <= raw := by omega
  have hrawLower : tangentMultiplicativeRatioCutoff lower rho raw < p.1 := by
    have h := tangentMultiplicativeRatioCutoff_rawCell_lt_label
      hlower hrho hpLower
    simpa only [raw, lower, bankPaperCanonicalRawRatioCellIndex, hpBand] using h
  have hnextLower :
      tangentMultiplicativeRatioCutoff lower rho (cut + 1) < p.1 := by
    exact (tangentMultiplicativeRatioCutoff_mono
      (lower := lower) (rho := rho) hrho.le hcutRaw).trans_lt hrawLower
  constructor
  · exact (Nat.min_le_left _ _).trans_lt (by
      simpa only [bankPaperCanonicalRatioCellTailLower, lower] using hnextLower)
  · simpa only [bankPaperCanonicalTangentPrimeLabel,
      bankPaperCanonicalRatioCellTailUpper] using hpUpper

/-! ## Uniform Mertens envelope on the concrete tails -/



/-- Uniform Mertens bounds the literal harmonic mass of every concrete
strict cell tail. -/
theorem bankPaperCanonical_ratioCellTail_harmonic_le_majorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) :
    tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
        band cut <=
      bankPaperCanonicalRatioCellTailMajorant
        M n W rho scale band cut := by
  apply tangentRatioCellTail_harmonicPointwiseUpper_le_uniformMajorant
    (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
    scale hscale band cut
    (bankPaperCanonicalRatioCellTailLower M n W rho band cut)
    (bankPaperCanonicalRatioCellTailUpper M n W band)
  · exact hMertens.trans
      (bankPaperCanonical_fixedCutoff_le_ratioCellTailLower
        M hdelta hn hW S hrho band cut)
  · exact bankPaperCanonicalRatioCellTailLower_le_upper
      M n W rho band cut
  · intro p hpBand hpCut
    exact bankPaperCanonical_ratioCellTail_mem_interval
      M hdelta hn hW S hrho band cut p hpBand hpCut

/-- The explicit tail majorant is nonnegative.  This is deduced from the
nonnegative literal harmonic tail rather than by separately manipulating
the log-log formula. -/
theorem bankPaperCanonicalRatioCellTailMajorant_nonneg
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (band : BankPaperCanonicalExponentBand M) (cut : Nat) :
    0 <= bankPaperCanonicalRatioCellTailMajorant
      M n W rho scale band cut := by
  have htailNonneg : 0 <=
      tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
        band cut := by
    unfold tangentRatioCellTailPointwiseUpper
    apply Finset.sum_nonneg
    intro p _hp
    by_cases htail :
        bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band ∧
          cut < bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p
    · simp only [if_pos htail]
      exact div_nonneg hscale (Nat.cast_nonneg _)
    · simp [htail]
  exact htailNonneg.trans
    (bankPaperCanonical_ratioCellTail_harmonic_le_majorant
      M hdelta hn hW S hrho hscale hMertens band cut)

/-! ## Quantitative PNT denominator inside an actual cell -/













/-! ## Finite traffic envelopes before the final mesh sum -/





































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRatioCellMomentTraffic -/
section


/-!
# Moment collapse of the canonical ratio-cell traffic

The endpoint-by-endpoint Mertens envelope is useful for pointwise ports,
but it is deliberately too wasteful for the sum over all cell cuts: its
uniform error is repeated once at every cut.  For total traffic one first
interchanges the two finite sums.  A vertex in cell `i` occurs in exactly
`i` strict tails, so the complete tail census is the first moment of the
literal cell index.

For the canonical multiplicative cells that index is at most

`(log y / log rho) * (t_p - t_lower)`.

The arithmetic moment bounds already proved for the canonical regular
mesh then give the paper-sized factor `delta + ratio`.  The only loss from
the natural floors is the explicit quantity `log 2 / log y`.

No new asymptotic or distribution hypothesis occurs in this file.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## The finite cut/tail interchange -/



/-! ## Logarithmic control of the concrete cell index -/





/-! ## The exact shifted-coordinate moment -/







/-! ## Canonical-mesh bound for the shifted moment -/









/-! ## Moment majorants for the complete traffic ledger -/











/-! ## Paper-scale scalar reduction -/







/-! ## Concrete geometry for the normalized pointwise port -/



/-- The current cell start remains beyond the fixed arithmetic cutoff. -/
theorem bankPaperCanonical_fixedCutoff_le_ratioCellCurrentLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    W <= bankPaperCanonicalRatioCellCurrentLower
      M hdelta hn hW S rho p := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn hW S p
  let cell := bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p
  exact (bankPaperCanonical_fixedCutoff_le_exponentBandLower
    M hdelta hn hW S band).trans (by
      have hmono := tangentMultiplicativeRatioCutoff_mono
        (lower := bankPaperCanonicalExponentBandLower M n W band)
        (rho := rho) hrho.le (Nat.zero_le cell)
      simpa only [bankPaperCanonicalRatioCellCurrentLower, band, cell,
        tangentMultiplicativeRatioCutoff_zero] using hmono)

/-- The start of the current merged cell lies strictly below its vertex. -/
theorem bankPaperCanonical_ratioCellCurrentLower_lt_label
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalRatioCellCurrentLower M hdelta hn hW S rho p <
      bankPaperCanonicalTangentPrimeLabel p := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn hW S p
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let raw := bankPaperCanonicalRawRatioCellIndex
    M hdelta hn hW S rho p
  let cell := bankPaperCanonicalRatioCellIndex
    M hdelta hn hW S rho p
  have hlower : 0 < lower :=
    bankPaperCanonicalExponentBandLower_pos M hdelta hn hW S band
  have hpLower : lower < p.1 := by
    simpa only [band, lower] using
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S p).1
  have hcellRaw : cell <= raw := by
    exact tangentMergedRatioCellIndex_le_raw _ _
  have hmono := tangentMultiplicativeRatioCutoff_mono
    (lower := lower) (rho := rho) hrho.le hcellRaw
  have hraw := tangentMultiplicativeRatioCutoff_rawCell_lt_label
    hlower hrho hpLower
  exact hmono.trans_lt (by
    simpa only [raw, lower, bankPaperCanonicalRawRatioCellIndex, band]
      using hraw)



/-! ## Scalar Mertens cancellation in one PNT-normalized port -/

/-- Moving the lower endpoint to the left can only enlarge the explicit
Mertens tail majorant. -/
theorem bankPaperCanonicalHarmonicTailMajorant_mono_lower
    {scale : Real} (hscale : 0 <= scale)
    {A B Y : Nat} (hA : 2 <= A) (hAB : A <= B) (hBY : B <= Y) :
    bankPaperCanonicalHarmonicTailMajorant scale B Y <=
      bankPaperCanonicalHarmonicTailMajorant scale A Y := by
  have hB : 2 <= B := hA.trans hAB
  have hY : 2 <= Y := hB.trans hBY
  have hAR : (0 : Real) < A := by positivity
  have hBR : (0 : Real) < B := by positivity
  have hYR : (0 : Real) < Y := by positivity
  have hlogA : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogB : 0 < Real.log (B : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogAB : Real.log (A : Real) <= Real.log (B : Real) :=
    Real.log_le_log hAR (by exact_mod_cast hAB)
  have hloglogAB :
      Real.log (Real.log (A : Real)) <=
        Real.log (Real.log (B : Real)) :=
    Real.log_le_log hlogA hlogAB
  have hpowAB : Real.log (A : Real) ^ 3 <=
      Real.log (B : Real) ^ 3 :=
    pow_le_pow_left₀ hlogA.le hlogAB 3
  have hconstant : 0 <=
      5 * fullReciprocalSumUniformConstant := by
    exact mul_nonneg (by norm_num)
      fullReciprocalSumUniformConstant_pos.le
  have herror :
      5 * fullReciprocalSumUniformConstant /
          Real.log (B : Real) ^ 3 <=
        5 * fullReciprocalSumUniformConstant /
          Real.log (A : Real) ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hlogB 3) (pow_pos hlogA 3)).2
    exact mul_le_mul_of_nonneg_left hpowAB hconstant
  unfold bankPaperCanonicalHarmonicTailMajorant
  apply mul_le_mul_of_nonneg_left _ hscale
  exact add_le_add (sub_le_sub_left hloglogAB _) herror

/-- The logarithm in a harmonic tail cancels the logarithm in the PNT
denominator. -/
theorem bankPaperCanonical_log_mul_logLogGap_le_logGap
    {A Y : Nat} (hA : 2 <= A) (hAY : A <= Y) :
    Real.log (A : Real) *
        (Real.log (Real.log (Y : Real)) -
          Real.log (Real.log (A : Real))) <=
      Real.log (Y : Real) - Real.log (A : Real) := by
  have hY : 2 <= Y := hA.trans hAY
  have hlogA : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogY : 0 < Real.log (Y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hratio : 0 < Real.log (Y : Real) / Real.log (A : Real) :=
    div_pos hlogY hlogA
  have hlog := Real.log_le_sub_one_of_pos hratio
  have hidentity :
      Real.log (Real.log (Y : Real)) -
          Real.log (Real.log (A : Real)) =
        Real.log (Real.log (Y : Real) / Real.log (A : Real)) := by
    rw [Real.log_div hlogY.ne' hlogA.ne']
  rw [hidentity]
  calc
    Real.log (A : Real) *
          Real.log (Real.log (Y : Real) / Real.log (A : Real)) <=
        Real.log (A : Real) *
          (Real.log (Y : Real) / Real.log (A : Real) - 1) :=
      mul_le_mul_of_nonneg_left hlog hlogA.le
    _ = Real.log (Y : Real) - Real.log (A : Real) := by
      field_simp [hlogA.ne']

/-- After multiplying by the denominator logarithm, two incident Mertens
tails cost at most twice the ordinary logarithmic gap plus the square-log
error. -/
theorem bankPaperCanonical_logCurrentLower_mul_portNumerator_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (p : BankPaperCanonicalTangentPrime n W) :
    let A := bankPaperCanonicalRatioCellCurrentLower
      M hdelta hn (by omega) S rho p
    let Y := bankPaperCanonicalExponentBandUpper M n W
      (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S p)
    Real.log (A : Real) *
        bankPaperCanonicalRatioCellPortNumeratorEnvelope
          M hdelta hn (by omega) S rho scale p <=
      2 * scale *
        (Real.log (Y : Real) - Real.log (A : Real) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 2) := by
  dsimp only
  let band := bankPaperCanonicalExponentBandOf M hdelta hn
    (by omega : W ≠ 0) S p
  let cell := bankPaperCanonicalRatioCellIndex M hdelta hn
    (by omega : W ≠ 0) S rho p
  let A := bankPaperCanonicalRatioCellCurrentLower
    M hdelta hn (by omega : W ≠ 0) S rho p
  let Y := bankPaperCanonicalExponentBandUpper M n W band
  have hWA : W <= A := by
    simpa only [A] using
      bankPaperCanonical_fixedCutoff_le_ratioCellCurrentLower
        M hdelta hn (by omega) S hrho p
  have hA2 : 2 <= A := hWtwo.trans hWA
  have hAY : A <= Y := by
    have hAp := bankPaperCanonical_ratioCellCurrentLower_lt_label
      M hdelta hn (by omega) S hrho p
    have hpY :=
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn (by omega) S p).2
    simpa only [A, Y, band] using hAp.le.trans hpY
  have hlogA : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  let baseMajorant := bankPaperCanonicalHarmonicTailMajorant scale A Y
  have htailCurrent :
      bankPaperCanonicalRatioCellTailMajorant
          M n W rho scale band cell <= baseMajorant := by
    let B := bankPaperCanonicalRatioCellTailLower M n W rho band cell
    have hAB : A <= B := by
      unfold A bankPaperCanonicalRatioCellCurrentLower B
        bankPaperCanonicalRatioCellTailLower
      apply le_min
      · exact tangentMultiplicativeRatioCutoff_mono
          (lower := bankPaperCanonicalExponentBandLower M n W band)
          (rho := rho) hrho.le (by omega)
      · exact hAY
    have hBY := bankPaperCanonicalRatioCellTailLower_le_upper
      M n W rho band cell
    exact bankPaperCanonicalHarmonicTailMajorant_mono_lower
      hscale hA2 hAB (by simpa only [B, Y,
        bankPaperCanonicalRatioCellTailUpper] using hBY)
  have htailPrevious :
      (if cell = 0 then 0
        else bankPaperCanonicalRatioCellTailMajorant
          M n W rho scale band (cell - 1)) <= baseMajorant := by
    by_cases hcell : cell = 0
    · simp [hcell]
      have hcurrentNonneg := bankPaperCanonicalRatioCellTailMajorant_nonneg
        M hdelta hn (by omega) S hrho hscale
        hMertens band cell
      exact hcurrentNonneg.trans htailCurrent
    · simp only [hcell, if_false]
      have hprevNext : cell - 1 + 1 = cell := by omega
      have htailLower :
          bankPaperCanonicalRatioCellTailLower M n W rho band (cell - 1) =
            A := by
        change min
          (tangentMultiplicativeRatioCutoff
            (bankPaperCanonicalExponentBandLower M n W band)
            rho (cell - 1 + 1))
          Y = A
        rw [hprevNext]
        exact Nat.min_eq_left hAY
      unfold bankPaperCanonicalRatioCellTailMajorant
      rw [htailLower]
      rfl
  have hnum :
      bankPaperCanonicalRatioCellPortNumeratorEnvelope
          M hdelta hn (by omega) S rho scale p <= 2 * baseMajorant := by
    unfold bankPaperCanonicalRatioCellPortNumeratorEnvelope
    simpa only [band, cell, two_mul] using
      add_le_add htailPrevious htailCurrent
  have hlogMain := bankPaperCanonical_log_mul_logLogGap_le_logGap hA2 hAY
  have hbaseIdentity :
      Real.log (A : Real) * baseMajorant =
        scale *
          (Real.log (A : Real) *
              (Real.log (Real.log (Y : Real)) -
                Real.log (Real.log (A : Real))) +
            5 * fullReciprocalSumUniformConstant /
              Real.log (A : Real) ^ 2) := by
    unfold baseMajorant bankPaperCanonicalHarmonicTailMajorant
    field_simp [hlogA.ne']
  calc
    Real.log (A : Real) *
          bankPaperCanonicalRatioCellPortNumeratorEnvelope
            M hdelta hn (by omega) S rho scale p <=
        Real.log (A : Real) * (2 * baseMajorant) :=
      mul_le_mul_of_nonneg_left hnum hlogA.le
    _ = 2 * (Real.log (A : Real) * baseMajorant) := by ring
    _ = 2 * scale *
        (Real.log (A : Real) *
            (Real.log (Real.log (Y : Real)) -
              Real.log (Real.log (A : Real))) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 2) := by
      rw [hbaseIdentity]
      ring
    _ <= 2 * scale *
        (Real.log (Y : Real) - Real.log (A : Real) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 2) := by
      gcongr



/-! ## Collapse of the remaining band endpoint gap -/





/-! ## Uniform paper-scale port envelope -/







/-! ## Paper-scale scalar reduction for the incident ledger -/











/-! ## A manifestly vanishing upper coefficient for total traffic -/











/-! ## Explicit fixed choices for the paper budgets -/





















end

end Erdos390.WholePaper

end

theorem solution :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) {n W : Nat}
  (hdelta :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta)
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
  (hWtwo : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W)
  (S : @Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation delta eta M n W) {rho scale : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) rho →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) scale →
      @LE.le.{0} Nat instLENat Erdos390.Full.PrimeBandQuadrature.fullReciprocalSumUniformCutoff W →
        ∀ (p : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W),
          let A :=
            @Erdos390.WholePaper.bankPaperCanonicalRatioCellCurrentLower delta eta M n W hdelta hn
              (fun (a : @Eq.{1} Nat W (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) =>
                @Erdos390.WholePaper.bankPaperCanonical_low_shiftedCoordinate_le._proof_1 n W hWtwo a)
              S rho p;
          let Y :=
            @Erdos390.WholePaper.bankPaperCanonicalExponentBandUpper delta eta M n W
              (@Erdos390.WholePaper.bankPaperCanonicalExponentBandOf delta eta M n W hdelta hn
                (fun (a : @Eq.{1} Nat W (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) =>
                  @Erdos390.WholePaper.bankPaperCanonical_low_shiftedCoordinate_le._proof_1 n W hWtwo a)
                S p);
          @LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (Real.log (@Nat.cast.{0} Real Real.instNatCast A))
              (@Erdos390.WholePaper.bankPaperCanonicalRatioCellPortNumeratorEnvelope delta eta M n W hdelta hn
                (fun (a : @Eq.{1} Nat W (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) =>
                  @Erdos390.WholePaper.bankPaperCanonical_low_shiftedCoordinate_le._proof_1 n W hWtwo a)
                S rho scale p))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                scale)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (Real.log (@Nat.cast.{0} Real Real.instNatCast Y)) (Real.log (@Nat.cast.{0} Real Real.instNatCast A)))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 5)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                    Erdos390.Full.PrimeBandQuadrature.fullReciprocalSumUniformConstant)
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid))
                    (Real.log (@Nat.cast.{0} Real Real.instNatCast A))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) := by
  exact @Erdos390.WholePaper.bankPaperCanonical_logCurrentLower_mul_portNumerator_le
