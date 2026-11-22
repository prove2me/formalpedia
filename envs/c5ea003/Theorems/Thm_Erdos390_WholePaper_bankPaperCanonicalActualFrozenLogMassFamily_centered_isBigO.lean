-- Prove2me | Theorems.Thm_Erdos390_WholePaper_bankPaperCanonicalActualFrozenLogMassFamily_centered_isBigO
-- name    : Erdos390.WholePaper.bankPaperCanonicalActualFrozenLogMassFamily_centered_isBigO
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:01:04.846671+00:00
-- url     : https://prove2.me/theorems/976ce897-7095-4ff4-b75d-cb30d553349e
-- title:
--   Centering the frozen logarithmic mass
-- statement:
--   Fix $c>0$ and structured sample data $D_n$ with finite nonempty head type, barycentric targets $T_n$, finite fixed, bank-base and candidate sets, preselectors and active seeds. Assume the actual active-measure constructor eventually holds, the canonical frozen interval geometry holds, and the canonical selector mass estimate holds. Let $\Lambda_0(n)$ and $m_0(n)$ be the corresponding literal frozen logarithmic and total masses. Then
--   $$\Lambda_0(n)-m_0(n)L(n)=O\!\left(\frac n{\log n}\right)\quad(n\to\infty),$$
--   with the right side interpreted as the repository's second-order scale.
--
--   This supplies the centered frozen ledger used by the bridge normalization.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSectionEightActualDataConnector.lean#L1371-L1508

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_008

universe u_1

theorem Erdos390.WholePaper.bankPaperCanonicalActualFrozenLogMassFamily_centered_isBigO :
∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] [inst_1 : Nonempty.{u_1 + 1} Head] {c : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c →
    ∀ (D : Nat → @Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head inst)
      (T : (n : Nat) → @Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1} Head inst (D n))
      (fixed bankBase candidates : Nat → Finset.{0} Nat) (preSelector : Nat → Nat → Real)
      (activeSeed : (n : Nat) → @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst (D n) → Real),
      @Filter.Eventually.{0} Nat
          (fun (n : Nat) =>
            @Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureConstructor.{u_1} Head inst inst_1 (D n) (T n)
              (candidates n) (preSelector n) (activeSeed n))
          (@Filter.atTop.{0} Nat Nat.instPreorder) →
        @Erdos390.WholePaper.BankPaperCanonicalActualFrozenIntervalGeometry c fixed bankBase candidates →
          Erdos390.WholePaper.BankPaperCanonicalActualSelectorMassEstimate c fixed bankBase candidates preSelector →
            @Asymptotics.IsBigO.{0, 0, 0} Nat Real Real Real.norm Real.norm (@Filter.atTop.{0} Nat Nat.instPreorder)
              (fun (n : Nat) =>
                @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@Erdos390.WholePaper.bankPaperCanonicalActualFrozenLogMassFamily.{u_1} Head inst D fixed bankBase
                    candidates preSelector activeSeed n)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Erdos390.WholePaper.bankPaperCanonicalActualFrozenTotalMassFamily.{u_1} Head inst D fixed bankBase
                      candidates preSelector activeSeed n)
                    (Erdos390.Full.Scale.L n)))
              Erdos390.WholePaper.secondOrderScale := by sorry
