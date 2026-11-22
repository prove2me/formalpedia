-- Prove2me | Theorems.Thm_Erdos390_WholePaper_bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval
-- name    : Erdos390.WholePaper.bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:05:10.842027+00:00
-- url     : https://prove2.me/theorems/ed300781-038e-4f1a-9abd-64ece05e0369
-- title:
--   Occupation of every canonical merged ratio cell
-- statement:
--   Let $M$ be a regular relative mesh with $\delta>0$, $n>1$, nonzero cutoff $W$, and scale separation, so its canonical prime partition is defined. Fix a ratio $\rho>1$. Assume the fixed-ratio prime-interval occupation property at cutoff $W$ and ratio $\rho$: for every natural $A\ge W$, the interval $(A,\lfloor\rho A\rfloor]$ has a prime. Then for every exponent band and every cell index through its last merged ratio cell,
--
--   $$N_{\rm cell}\ne0.$$
--
--   The possibly short final fragment need not contain a prime separately because it is merged with the preceding full cell.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalRatioCellGeometry.lean#L569-L707

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

theorem Erdos390.WholePaper.bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval :
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
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := by sorry
