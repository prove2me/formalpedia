-- Prove2me | solution 1 for Erdos390.WholePaper.bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T13:21:17.833605+00:00
-- url     : https://prove2.me/submissions/f91cb76c-f850-4779-b298-1549688c94af

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Definitions.Def_erdos390_analytic_foundations_001
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_010

theorem ped_pc_sub_le (c b : ℕ) :
    Nat.primeCounting b - Nat.primeCounting c ≤ ((Finset.Ioc c b).filter Nat.Prime).card := by
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting]
  have h : Nat.primesLE b ⊆ Nat.primesLE c ∪ (Finset.Ioc c b).filter Nat.Prime := by
    intro q hq
    rw [Nat.mem_primesLE] at hq
    rw [Finset.mem_union, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    by_cases hqc : q ≤ c
    · exact Or.inl ⟨hqc, hq.2⟩
    · exact Or.inr ⟨⟨by omega, hq.1⟩, hq.2⟩
  have := (Finset.card_le_card h).trans (Finset.card_union_le _ _)
  omega

theorem ped_cut_mono (L : ℕ) {rho : ℝ} (hrho : 1 ≤ rho) {i j : ℕ} (hij : i ≤ j) :
    Erdos390.WholePaper.tangentMultiplicativeRatioCutoff L rho i ≤ Erdos390.WholePaper.tangentMultiplicativeRatioCutoff L rho j :=
  Nat.floor_mono (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hrho hij) (Nat.cast_nonneg L))

theorem ped_lower_le_cut (L : ℕ) {rho : ℝ} (hrho : 1 ≤ rho) (k : ℕ) :
    L ≤ Erdos390.WholePaper.tangentMultiplicativeRatioCutoff L rho k := by
  apply Nat.le_floor
  have : (1:ℝ) ≤ rho ^ k := one_le_pow₀ hrho
  have hL : (0:ℝ) ≤ L := Nat.cast_nonneg L
  nlinarith

theorem ped_step_le (L : ℕ) {rho : ℝ} (hrho : 1 ≤ rho) (k : ℕ) :
    ⌊rho * (Erdos390.WholePaper.tangentMultiplicativeRatioCutoff L rho k : ℝ)⌋₊ ≤
      Erdos390.WholePaper.tangentMultiplicativeRatioCutoff L rho (k + 1) := by
  apply Nat.floor_mono
  have hx : (0:ℝ) ≤ (L:ℝ) * rho ^ k :=
    mul_nonneg (Nat.cast_nonneg L) (pow_nonneg (by linarith) k)
  have h1 : ((Erdos390.WholePaper.tangentMultiplicativeRatioCutoff L rho k : ℕ) : ℝ) ≤ (L:ℝ) * rho ^ k :=
    Nat.floor_le hx
  calc rho * (Erdos390.WholePaper.tangentMultiplicativeRatioCutoff L rho k : ℝ) ≤ rho * ((L:ℝ) * rho ^ k) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = (L:ℝ) * rho ^ (k + 1) := by ring

theorem ped_pos_of_lt_raw {L x cell : ℕ} {rho : ℝ}
    (h : cell < Erdos390.WholePaper.tangentMultiplicativeRawCellIndex L x rho) : 0 < L ∧ 1 < rho := by
  unfold Erdos390.WholePaper.tangentMultiplicativeRawCellIndex at h
  by_contra hc
  rw [dif_neg hc] at h
  omega

theorem ped_cut_lt_of_lt_raw {L x cell : ℕ} {rho : ℝ}
    (h : cell < Erdos390.WholePaper.tangentMultiplicativeRawCellIndex L x rho) :
    Erdos390.WholePaper.tangentMultiplicativeRatioCutoff L rho (cell + 1) < x := by
  have hp := ped_pos_of_lt_raw h
  unfold Erdos390.WholePaper.tangentMultiplicativeRawCellIndex at h
  rw [dif_pos hp] at h
  have := Nat.find_min _ h
  omega

theorem ped_raw_eq {L q cell : ℕ} {rho : ℝ} (hL : 0 < L) (hrho : 1 < rho)
    (hlo : Erdos390.WholePaper.tangentMultiplicativeRatioCutoff L rho cell < q)
    (hhi : q ≤ Erdos390.WholePaper.tangentMultiplicativeRatioCutoff L rho (cell + 1)) :
    Erdos390.WholePaper.tangentMultiplicativeRawCellIndex L q rho = cell := by
  unfold Erdos390.WholePaper.tangentMultiplicativeRawCellIndex
  rw [dif_pos ⟨hL, hrho⟩, Nat.find_eq_iff]
  refine ⟨hhi, fun k hk hle => ?_⟩
  have := ped_cut_mono L hrho.le (show k + 1 ≤ cell by omega)
  omega

set_option maxHeartbeats 4000000 in
open Erdos390.WholePaper in
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
  intro delta eta M n W hdelta hn hW S rho hrho hocc band cell hcell
  have hcell' : cell ≤ bankPaperCanonicalLastRawRatioCell M (n := n) (W := W) rho band - 1 := hcell
  have hWL : W ≤ bankPaperCanonicalExponentBandLower M n W band :=
    (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalCertificate M hdelta hn hW S).cutoff_le_lower band
  have hUy : bankPaperCanonicalExponentBandUpper M n W band ≤ Erdos390.Full.ArithmeticModel.yNat n :=
    (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalCertificate M hdelta hn hW S).upper_le_yNat band
  have hL0 : 0 < bankPaperCanonicalExponentBandLower M n W band := by omega
  -- a prime q in the band whose merged index is `cell` gives a nonzero card
  suffices h : ∃ q : ℕ, q.Prime ∧ bankPaperCanonicalExponentBandLower M n W band < q ∧
      q ≤ bankPaperCanonicalExponentBandUpper M n W band ∧
      tangentMergedRatioCellIndex (bankPaperCanonicalLastRawRatioCell M (n := n) (W := W) rho band)
        (tangentMultiplicativeRawCellIndex (bankPaperCanonicalExponentBandLower M n W band) q rho) = cell by
    obtain ⟨q, hqp, hLq, hqU, hidx⟩ := h
    have hmem : q ∈ Erdos390.Full.ArithmeticModel.primeBand n W :=
      Erdos390.Full.ArithmeticModel.mem_primeBand.mpr ⟨hqp, by omega, by omega⟩
    have hband : bankPaperCanonicalExponentBandOf M hdelta hn hW S ⟨q, hmem⟩ = band :=
      ((Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalCertificate M hdelta hn hW S).band_eq_iff
        ⟨q, hmem⟩ band).2 ⟨hLq, hqU⟩
    unfold tangentRatioCellCard
    apply Finset.card_ne_zero_of_mem (a := ⟨q, hmem⟩)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hband, ?_⟩
    show tangentMergedRatioCellIndex
      (bankPaperCanonicalLastRawRatioCell M (n := n) (W := W) rho
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S ⟨q, hmem⟩))
      (tangentMultiplicativeRawCellIndex
        (bankPaperCanonicalExponentBandLower M n W
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S ⟨q, hmem⟩)) q rho) = cell
    rw [hband]
    exact hidx
  by_cases hlt : cell < bankPaperCanonicalLastRawRatioCell M (n := n) (W := W) rho band
  · have hlt' : cell < tangentMultiplicativeRawCellIndex
        (bankPaperCanonicalExponentBandLower M n W band)
        (bankPaperCanonicalExponentBandUpper M n W band) rho := hlt
    have hcutU := ped_cut_lt_of_lt_raw hlt'
    have hstep := ped_step_le (bankPaperCanonicalExponentBandLower M n W band) hrho.le cell
    have hLc := ped_lower_le_cut (bankPaperCanonicalExponentBandLower M n W band) hrho.le cell
    obtain ⟨q, hqp, hAq, hqB⟩ := hocc
      (tangentMultiplicativeRatioCutoff (bankPaperCanonicalExponentBandLower M n W band) rho cell)
      (by omega)
    refine ⟨q, hqp, by omega, by omega, ?_⟩
    rw [ped_raw_eq hL0 hrho hAq (by omega)]
    unfold tangentMergedRatioCellIndex
    omega
  · have hcell0 : cell = 0 := by omega
    have hlast0 : bankPaperCanonicalLastRawRatioCell M (n := n) (W := W) rho band = 0 := by omega
    obtain ⟨q, hqp, hLq, hqU⟩ :=
      Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.every_fullCutoff_cell_has_prime M hW S band
    refine ⟨q, hqp, hLq, hqU, ?_⟩
    rw [hlast0]
    unfold tangentMergedRatioCellIndex
    omega
