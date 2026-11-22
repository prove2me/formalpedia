-- Prove2me | Definitions.Def_erdos390_analytic_compact_goals_005
-- name    : erdos390_analytic_compact_goals_005
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T17:07:33.551355+00:00
-- url     : https://prove2.me/theorems/805c301e-398d-48fb-bdc6-da8a7dc96476
-- title:
--   Explicit propositions for four analytic comparison estimates
-- statement:
--   This file names the fully quantified proposition that the canonical weighted prime-number-theorem envelope is bounded by the logarithmic gap. It preserves every original parameter, hypothesis, and universe level, and is definitionally identical to Erdos390.WholePaper.bankPaperCanonical_weightedPNTEnvelope_le_logGap. Naming the proposition asserts no new fact or axiom.
-- source:
--   https://github.com/ShouqiaoW/erdos/tree/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean

import Definitions.Def_erdos390_analytic_foundations_001
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_010
import Definitions.Def_erdos390_analytic_statement_auxiliaries
import Definitions.Def_erdos390_dickman_step_function
import Definitions.Def_erdos390_source_bank_interface
import Mathlib
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_MediumPNT

set_option maxRecDepth 10000
set_option maxHeartbeats 0

noncomputable def Erdos390.AnalyticCompactBatch005Goal001 : Prop :=
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
              (@Nat.cast.{0} Real Real.instNatCast (@Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel n W p))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Erdos390.WholePaper.bankPaperCanonicalRatioCellPortNumeratorEnvelope delta eta M n W hdelta hn
                  (fun (a : @Eq.{1} Nat W (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) =>
                    @Erdos390.WholePaper.bankPaperCanonical_low_shiftedCoordinate_le._proof_1 n W hWtwo a)
                  S rho scale p)
                (@Erdos390.WholePaper.bankPaperCanonicalRatioCellPNTDenominator delta eta M n W hdelta hn
                  (fun (a : @Eq.{1} Nat W (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) =>
                    @Erdos390.WholePaper.bankPaperCanonical_low_shiftedCoordinate_le._proof_1 n W hWtwo a)
                  S rho p)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 8)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid)) rho
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) rho
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
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
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))


