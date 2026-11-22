-- Prove2me | solution 1 for Erdos390.WholePaper.bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:17:44.718514+00:00
-- url     : https://prove2.me/submissions/f2f9fabb-f1f7-4dad-aac3-472da8fbe2f3

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



/-- The full raw cells of every canonical exponent band are occupied once
the fixed-ratio PNT input is available.  The possibly short final raw
fragment is not required to be occupied separately because it is merged
into the preceding cell. -/
theorem bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (hprime : TangentFixedRatioPrimeIntervalOccupied W rho) :
    forall (band : BankPaperCanonicalExponentBand M) (cell : Nat),
      cell <= bankPaperCanonicalLastRatioCell M
        (n := n) (W := W) rho band ->
        tangentRatioCellCard
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
          band cell ≠ 0 := by
  intro band cell hcell
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S
  let E := RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
    M hdelta hn hW S
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let upper := bankPaperCanonicalExponentBandUpper M n W band
  let lastRaw := bankPaperCanonicalLastRawRatioCell M
    (n := n) (W := W) rho band
  have hlower : 0 < lower := by
    exact bankPaperCanonicalExponentBandLower_pos
      M hdelta hn hW S band
  by_cases hlast : lastRaw = 0
  · have hcellZero : cell = 0 := by
      have hcellLe : cell <= 0 := by
        simpa [bankPaperCanonicalLastRatioCell,
          tangentMergedRatioLastCell, lastRaw, hlast] using hcell
      exact Nat.eq_zero_of_le_zero hcellLe
    obtain ⟨p, hpBand⟩ := P.fiber_nonempty band
    have hpMerged :
        bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p = 0 := by
      unfold bankPaperCanonicalRatioCellIndex
      rw [show bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band by
        simpa only [P, bankPaperCanonicalExponentBandOf] using hpBand]
      simp [lastRaw, hlast, tangentMergedRatioCellIndex]
    unfold tangentRatioCellCard
    rw [← Nat.pos_iff_ne_zero]
    apply Finset.card_pos.mpr
    exact ⟨p, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by simpa only [P, bankPaperCanonicalExponentBandOf] using hpBand,
        hpMerged.trans hcellZero.symm⟩⟩
  · have hcellRaw : cell < lastRaw := by
      have hcell' : cell <= lastRaw - 1 := by
        simpa only [bankPaperCanonicalLastRatioCell,
          tangentMergedRatioLastCell, lastRaw] using hcell
      omega
    let A := tangentMultiplicativeRatioCutoff lower rho cell
    have hWLower : W <= lower := by
      have hcut := E.cutoff_le_lower band
      simpa only [E, lower, bankPaperCanonicalExponentBandLower,
        RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower] using hcut
    have hlowerBoundary : (lower : Real) <=
        (lower : Real) * rho ^ cell := by
      nth_rewrite 1 [← mul_one (lower : Real)]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg lower)
      exact one_le_pow₀ (by linarith)
    have hlowerA : lower <= A := by
      apply Nat.le_floor
      exact hlowerBoundary
    have hWA : W <= A := hWLower.trans hlowerA
    obtain ⟨p, hpPrime, hpLower, hpUpper⟩ := hprime A hWA
    have hAReal : (A : Real) <= (lower : Real) * rho ^ cell := by
      exact Nat.floor_le
        (mul_nonneg (Nat.cast_nonneg lower) (pow_nonneg (by linarith) _))
    have hrhoNonneg : 0 <= rho := by linarith
    have hnextReal : rho * (A : Real) <=
        (lower : Real) * rho ^ (cell + 1) := by
      calc
        rho * (A : Real) <= rho * ((lower : Real) * rho ^ cell) :=
          mul_le_mul_of_nonneg_left hAReal hrhoNonneg
        _ = (lower : Real) * rho ^ (cell + 1) := by
          rw [pow_succ]
          ring
    have hpNext : p <=
        tangentMultiplicativeRatioCutoff lower rho (cell + 1) := by
      exact hpUpper.trans (Nat.floor_mono hnextReal)
    have hcutMono := tangentMultiplicativeRatioCutoff_mono
      (lower := lower) (rho := rho) hrho.le
    have hlastLower :
        tangentMultiplicativeRatioCutoff lower rho lastRaw < upper := by
      have hupperStrict : lower < upper := by
        obtain ⟨q, hq⟩ := P.fiber_nonempty band
        have hqInterval := (E.band_eq_iff q band).mp hq
        exact hqInterval.1.trans_le hqInterval.2
      simpa only [lastRaw, upper, lower,
        bankPaperCanonicalLastRawRatioCell] using
        tangentMultiplicativeRatioCutoff_rawCell_lt_label
          hlower hrho hupperStrict
    have hpUpperBand : p <= upper := by
      exact hpNext.trans
        ((hcutMono (by omega : cell + 1 <= lastRaw)).trans
          hlastLower.le)
    have hpBandNat : p ∈ primeBand n W := by
      apply mem_primeBand.mpr
      exact ⟨hpPrime, hWA.trans_lt hpLower,
        hpUpperBand.trans (by
          simpa only [E, upper, bankPaperCanonicalExponentBandUpper,
            RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_upper] using
              E.upper_le_yNat band)⟩
    let q : BankPaperCanonicalTangentPrime n W := ⟨p, hpBandNat⟩
    have hqBand :
        bankPaperCanonicalExponentBandOf M hdelta hn hW S q = band := by
      have hinterval : E.lower band < q.1 ∧ q.1 <= E.upper band := by
        constructor
        · have hLowerBand : lower <= A := hlowerA
          have : lower < p := hLowerBand.trans_lt hpLower
          simpa only [E, lower, bankPaperCanonicalExponentBandLower,
            RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower] using this
        · simpa only [E, upper, bankPaperCanonicalExponentBandUpper,
            RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_upper] using
              hpUpperBand
      have := (E.band_eq_iff q band).mpr hinterval
      simpa only [P, bankPaperCanonicalExponentBandOf] using this
    have hqRaw :
        bankPaperCanonicalRawRatioCellIndex
          M hdelta hn hW S rho q = cell := by
      unfold bankPaperCanonicalRawRatioCellIndex
      rw [hqBand]
      exact tangentMultiplicativeRawCellIndex_eq_of_mem
        hlower hrho hpLower hpNext
    have hqCell :
        bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho q = cell := by
      unfold bankPaperCanonicalRatioCellIndex
      rw [hqBand, hqRaw]
      exact tangentMergedRatioCellIndex_eq_self hcell
    unfold tangentRatioCellCard
    rw [← Nat.pos_iff_ne_zero]
    apply Finset.card_pos.mpr
    exact ⟨q, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hqBand, hqCell⟩⟩



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
    Erdos390.WholePaper.TangentFixedRatioPrimeIntervalOccupied W rho →
      ∀ (band : @Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) (cell : Nat),
        @LE.le.{0} Nat instLENat cell (@Erdos390.WholePaper.bankPaperCanonicalLastRatioCell delta eta M n W rho band) →
          @Ne.{1} Nat
            (@Erdos390.WholePaper.tangentRatioCellCard.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (@Erdos390.Full.ArithmeticBandGeometry.Partition.instFintypeBandPrime n W)
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Erdos390.WholePaper.bankPaperCanonicalExponentBandOf delta eta M n W hdelta hn hW S)
              (@Erdos390.WholePaper.bankPaperCanonicalRatioCellIndex delta eta M n W hdelta hn hW S rho) band cell)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := by
  exact @Erdos390.WholePaper.bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval
