-- Prove2me | Theorems.Thm_Erdos390_WholePaper_bankPaperCanonical_fixedRatioPrimeCounting_le_ratioCellCard
-- name    : Erdos390.WholePaper.bankPaperCanonical_fixedRatioPrimeCounting_le_ratioCellCard
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:02:34.1403+00:00
-- url     : https://prove2.me/theorems/176745c3-b05d-451b-9c02-3371b445aa6a
-- title:
--   Prime-counting lower bound for a canonical ratio cell
-- statement:
--   Let $M$ be a regular relative mesh with $\delta>0$, $n>1$, nonzero cutoff $W$, and scale separation, so its canonical prime partition is defined. Fix a ratio $\rho>1$. For an exponent band and raw cell index $j$ strictly below its last raw ratio cell, let $A$ be the multiplicative ratio cutoff at the beginning of that cell. If $N_{\rm cell}$ is the cardinality of the corresponding merged ratio cell, then
--
--   $$\pi(\lfloor\rho A\rfloor)-\pi(A)\le N_{\rm cell}.$$
--
--   A full raw prime interval injects into the merged cell, which may additionally contain the final short fragment.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalRatioCellTraffic.lean#L301-L435

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

theorem Erdos390.WholePaper.bankPaperCanonical_fixedRatioPrimeCounting_le_ratioCellCard :
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
            (@Erdos390.WholePaper.bankPaperCanonicalRatioCellIndex delta eta M n W hdelta hn hW S rho) band cell) := by sorry
