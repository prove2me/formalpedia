-- Prove2me | solution 1 for Erdos390.WholePaper.bankPaperCanonical_fixedRatioPrimeCounting_le_ratioCellCard_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:17:01.47592+00:00
-- url     : https://prove2.me/submissions/aad4f05d-b019-49f9-b471-9899bd786498

import Definitions.Def_erdos390_analytic_compact_goals_002
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

















/-- The cardinality of a natural prime interval is the corresponding
difference of the totalized prime-counting function. -/
theorem prime_Ioc_card_eq_primeCounting_sub {a b : ℕ} (hab : a ≤ b) :
    ((Finset.Ioc a b).filter Nat.Prime).card =
      Nat.primeCounting b - Nat.primeCounting a := by
  classical
  have hdiff :
      (Finset.Ioc a b).filter Nat.Prime =
        (Finset.range (b + 1)).filter Nat.Prime \
          (Finset.range (a + 1)).filter Nat.Prime := by
    ext prime
    by_cases hp : prime.Prime
    · simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
        Finset.mem_range, hp, and_true]
      omega
    · simp [hp]
  have hsubset :
      (Finset.range (a + 1)).filter Nat.Prime ⊆
        (Finset.range (b + 1)).filter Nat.Prime := by
    intro prime hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1.trans_le (Nat.add_le_add_right hab 1), hp.2⟩
  rw [hdiff, Finset.card_sdiff_of_subset hsubset]
  simp only [Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]





end

end Erdos390.WholePaper.SafePrimeCounting

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













/-! ## Instantiation of the star split-request boundary -/





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





theorem label_le_tangentMultiplicativeRatioCutoff_rawCell_succ
    {lower label : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) :
    label <= tangentMultiplicativeRatioCutoff lower rho
      (tangentMultiplicativeRawCellIndex lower label rho + 1) := by
  unfold tangentMultiplicativeRawCellIndex
  rw [dif_pos ⟨hlower, hrho⟩]
  exact Nat.find_spec
    (exists_label_le_tangentMultiplicativeRatioCutoff_succ
      hlower hrho label)

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



theorem tangentMultiplicativeRawCellIndex_eq_of_mem
    {lower label cell : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho)
    (hlowerCell : tangentMultiplicativeRatioCutoff lower rho cell < label)
    (hupperCell : label <=
      tangentMultiplicativeRatioCutoff lower rho (cell + 1)) :
    tangentMultiplicativeRawCellIndex lower label rho = cell := by
  have hle : tangentMultiplicativeRawCellIndex lower label rho <= cell := by
    unfold tangentMultiplicativeRawCellIndex
    rw [dif_pos ⟨hlower, hrho⟩]
    exact Nat.find_min'
      (exists_label_le_tangentMultiplicativeRatioCutoff_succ
        hlower hrho label) hupperCell
  apply Nat.le_antisymm hle
  by_contra hnot
  have hlt : tangentMultiplicativeRawCellIndex lower label rho < cell :=
    Nat.lt_of_not_ge hnot
  have hrawUpper :=
    label_le_tangentMultiplicativeRatioCutoff_rawCell_succ
      hlower hrho (label := label)
  have hcutMono := tangentMultiplicativeRatioCutoff_mono
    (lower := lower) (rho := rho) hrho.le
  have hcut : tangentMultiplicativeRatioCutoff lower rho
      (tangentMultiplicativeRawCellIndex lower label rho + 1) <=
        tangentMultiplicativeRatioCutoff lower rho cell :=
    hcutMono (by omega)
  omega





/-! ## Merging the terminal fragment -/









theorem tangentMergedRatioCellIndex_eq_self
    {lastRaw raw : Nat} (hraw : raw <= tangentMergedRatioLastCell lastRaw) :
    tangentMergedRatioCellIndex lastRaw raw = raw := by
  exact Nat.min_eq_left hraw











/-! ## The canonical paper exponent bands -/











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





/-! ## Uniform Mertens envelope on the concrete tails -/







/-! ## Quantitative PNT denominator inside an actual cell -/







/-- The last raw cutoff is strictly below the exponent-band upper endpoint.
This is the finite fact that keeps every earlier full raw interval inside
the canonical prime band. -/
theorem bankPaperCanonical_lastRawRatioCutoff_lt_bandUpper
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (band : BankPaperCanonicalExponentBand M) :
    tangentMultiplicativeRatioCutoff
        (bankPaperCanonicalExponentBandLower M n W band) rho
        (bankPaperCanonicalLastRawRatioCell M
          (n := n) (W := W) rho band) <
      bankPaperCanonicalExponentBandUpper M n W band := by
  obtain ⟨p, hp⟩ :=
    (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hn hW S).fiber_nonempty band
  have hpInterval :=
    ((RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
      M hdelta hn hW S).band_eq_iff p band).mp hp
  have hstrict : bankPaperCanonicalExponentBandLower M n W band <
      bankPaperCanonicalExponentBandUpper M n W band :=
    hpInterval.1.trans_le hpInterval.2
  simpa only [bankPaperCanonicalLastRawRatioCell] using
    tangentMultiplicativeRatioCutoff_rawCell_lt_label
      (bankPaperCanonicalExponentBandLower_pos M hdelta hn hW S band)
      hrho hstrict

/-- The primes in the full raw interval beginning at a merged cell inject
into the literal finite cell.  The final raw fragment may also be present
in the target cell, so the result is an inequality rather than an equality. -/
theorem bankPaperCanonical_fixedRatioPrimeCounting_le_ratioCellCard
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (band : BankPaperCanonicalExponentBand M) (cell : Nat)
    (hcell : cell < bankPaperCanonicalLastRawRatioCell M
      (n := n) (W := W) rho band) :
    Nat.primeCounting
          ⌊rho * (tangentMultiplicativeRatioCutoff
            (bankPaperCanonicalExponentBandLower M n W band)
            rho cell : Real)⌋₊ -
        Nat.primeCounting
          (tangentMultiplicativeRatioCutoff
            (bankPaperCanonicalExponentBandLower M n W band) rho cell) <=
      tangentRatioCellCard
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
        band cell := by
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let lastRaw := bankPaperCanonicalLastRawRatioCell M
    (n := n) (W := W) rho band
  let A := tangentMultiplicativeRatioCutoff lower rho cell
  let B := ⌊rho * (A : Real)⌋₊
  let source : Finset Nat := (Finset.Ioc A B).filter Nat.Prime
  let target : Finset (BankPaperCanonicalTangentPrime n W) :=
    Finset.univ.filter (fun p =>
      bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band ∧
        bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p = cell)
  let labelEmbedding : BankPaperCanonicalTangentPrime n W ↪ Nat :=
    ⟨bankPaperCanonicalTangentPrimeLabel,
      bankPaperCanonicalTangentPrimeLabel_injective⟩
  let targetLabels : Finset Nat := target.map labelEmbedding
  have hlower : 0 < lower :=
    bankPaperCanonicalExponentBandLower_pos M hdelta hn hW S band
  have hALower : lower <= A := by
    have hmono := tangentMultiplicativeRatioCutoff_mono
      (lower := lower) (rho := rho) hrho.le (Nat.zero_le cell)
    simpa only [A, tangentMultiplicativeRatioCutoff_zero] using hmono
  have hAB : A <= B := by
    apply Nat.le_floor
    have hrhoNonneg : 0 <= rho := by linarith
    calc
      (A : Real) = 1 * (A : Real) := by ring
      _ <= rho * (A : Real) :=
        mul_le_mul_of_nonneg_right hrho.le (Nat.cast_nonneg A)
  have hsubset : source ⊆ targetLabels := by
    intro p hpSource
    have hpFilter := Finset.mem_filter.mp hpSource
    have hpIoc := Finset.mem_Ioc.mp hpFilter.1
    have hpPrime : p.Prime := hpFilter.2
    have hAReal : (A : Real) <= (lower : Real) * rho ^ cell := by
      exact Nat.floor_le
        (mul_nonneg (Nat.cast_nonneg lower) (pow_nonneg (by linarith) _))
    have hnextReal : rho * (A : Real) <=
        (lower : Real) * rho ^ (cell + 1) := by
      calc
        rho * (A : Real) <= rho * ((lower : Real) * rho ^ cell) :=
          mul_le_mul_of_nonneg_left hAReal (by linarith)
        _ = (lower : Real) * rho ^ (cell + 1) := by
          rw [pow_succ]
          ring
    have hpNext : p <= tangentMultiplicativeRatioCutoff
        lower rho (cell + 1) := by
      exact hpIoc.2.trans (Nat.floor_mono hnextReal)
    have hnextLast : tangentMultiplicativeRatioCutoff lower rho (cell + 1) <=
        tangentMultiplicativeRatioCutoff lower rho lastRaw := by
      exact tangentMultiplicativeRatioCutoff_mono
        (lower := lower) (rho := rho) hrho.le (by omega)
    have hpUpperBand : p <=
        bankPaperCanonicalExponentBandUpper M n W band := by
      exact hpNext.trans (hnextLast.trans
        (by simpa only [lower, lastRaw] using
          (bankPaperCanonical_lastRawRatioCutoff_lt_bandUpper
            M hdelta hn hW S hrho band).le))
    have hWLower := bankPaperCanonical_fixedCutoff_le_exponentBandLower
      M hdelta hn hW S band
    have hpBandNat : p ∈ primeBand n W := by
      apply mem_primeBand.mpr
      exact ⟨hpPrime, (hWLower.trans hALower).trans_lt hpIoc.1,
        hpUpperBand.trans (by
          simpa only [bankPaperCanonicalExponentBandUpper,
            RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_upper] using
              (RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
                M hdelta hn hW S).upper_le_yNat band)⟩
    let q : BankPaperCanonicalTangentPrime n W := ⟨p, hpBandNat⟩
    have hqBand :
        bankPaperCanonicalExponentBandOf M hdelta hn hW S q = band := by
      have hinterval :
          (RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
              M hdelta hn hW S).lower band < q.1 ∧
            q.1 <=
              (RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
                M hdelta hn hW S).upper band := by
        constructor
        · have : lower < p := hALower.trans_lt hpIoc.1
          simpa only [lower,
            RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower] using this
        · simpa only [bankPaperCanonicalExponentBandUpper,
            RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_upper] using
              hpUpperBand
      have hband :=
        ((RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
          M hdelta hn hW S).band_eq_iff q band).mpr hinterval
      simpa only [bankPaperCanonicalExponentBandOf] using hband
    have hqRaw : bankPaperCanonicalRawRatioCellIndex
        M hdelta hn hW S rho q = cell := by
      unfold bankPaperCanonicalRawRatioCellIndex
      rw [hqBand]
      exact tangentMultiplicativeRawCellIndex_eq_of_mem
        hlower hrho hpIoc.1 hpNext
    have hqCell : bankPaperCanonicalRatioCellIndex
        M hdelta hn hW S rho q = cell := by
      unfold bankPaperCanonicalRatioCellIndex
      rw [hqBand, hqRaw]
      exact tangentMergedRatioCellIndex_eq_self (by
        unfold tangentMergedRatioLastCell
        simpa only [lastRaw] using (show cell <= lastRaw - 1 by omega))
    apply Finset.mem_map.mpr
    exact ⟨q, by
      simp only [target, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hqBand, hqCell⟩, rfl⟩
  have hcard : source.card <= targetLabels.card :=
    Finset.card_le_card hsubset
  have hsource : source.card =
      Nat.primeCounting B - Nat.primeCounting A := by
    simpa only [source] using
      SafePrimeCounting.prime_Ioc_card_eq_primeCounting_sub hAB
  have htarget : targetLabels.card = target.card := by
    exact Finset.card_map labelEmbedding
  rw [hsource, htarget] at hcard
  simpa only [target, A, B, lower, tangentRatioCellCard] using hcard



/-! ## Finite traffic envelopes before the final mesh sum -/





































end

end Erdos390.WholePaper

end

theorem solution :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) {n W : Nat}
  (hdelta :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta)
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
  (hW : @Ne.{1} Nat W (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (S : @Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation delta eta M n W) {rho : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) rho →
    ∀ (band : @Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) (cell : Nat),
      @LT.lt.{0} Nat instLTNat cell (@Erdos390.WholePaper.bankPaperCanonicalLastRawRatioCell delta eta M n W rho band) →
        @LE.le.{0} Nat instLENat
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instIsOrderedRing
                  Real.instFloorRing)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) rho
                  (@Nat.cast.{0} Real Real.instNatCast
                    (Erdos390.WholePaper.tangentMultiplicativeRatioCutoff
                      (@Erdos390.WholePaper.bankPaperCanonicalExponentBandLower delta eta M n W band) rho
                      cell)))).primeCounting
            (Erdos390.WholePaper.tangentMultiplicativeRatioCutoff
                (@Erdos390.WholePaper.bankPaperCanonicalExponentBandLower delta eta M n W band) rho cell).primeCounting)
          (@Erdos390.WholePaper.tangentRatioCellCard.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
            (@Erdos390.Full.ArithmeticBandGeometry.Partition.instFintypeBandPrime n W)
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Erdos390.WholePaper.bankPaperCanonicalExponentBandOf delta eta M n W hdelta hn hW S)
            (@Erdos390.WholePaper.bankPaperCanonicalRatioCellIndex delta eta M n W hdelta hn hW S rho) band cell) := by
  exact @Erdos390.WholePaper.bankPaperCanonical_fixedRatioPrimeCounting_le_ratioCellCard
