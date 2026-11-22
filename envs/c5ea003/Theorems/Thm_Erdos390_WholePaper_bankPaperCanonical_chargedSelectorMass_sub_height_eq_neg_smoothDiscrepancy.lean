-- Prove2me | Theorems.Thm_Erdos390_WholePaper_bankPaperCanonical_chargedSelectorMass_sub_height_eq_neg_smoothDiscrepancy
-- name    : Erdos390.WholePaper.bankPaperCanonical_chargedSelectorMass_sub_height_eq_neg_smoothDiscrepancy
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:02:25.203427+00:00
-- url     : https://prove2.me/theorems/a7b3b6ed-f6b8-4d1e-9103-ac22c70105dc
-- title:
--   Charged selector mass equals the remaining smooth-row discrepancy
-- statement:
--   Let $R$ be a bank realization on the interval with tail height $h$, equipped with any compatible guarded anchor certificate. Fix $\delta$, $K$ and a selector $s$ on its guarded candidates $A$. Assume every attained active nonexceptional rough row has exactly its postcharge target mass, every attained exceptional row other than label one has zero mass, and every complete active nonexceptional label has postcharge capacity. Writing $G$ for fixed exceptional factors, $B_0$ for the precharge base state, and $\Delta_1(s)$ for the smooth-row postcharge discrepancy, one has
--   $$|G|+|B_0|+\sum_{a\in A}s(a)-h=-\Delta_1(s).$$
--
--   The identity isolates the single smooth-row mass correction after all nonsmooth rows have been fixed.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSectionEightActualDataConnector.lean#L461-L693

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008

theorem Erdos390.WholePaper.bankPaperCanonical_chargedSelectorMass_sub_height_eq_neg_smoothDiscrepancy :
∀ {c : Real} {depth n h K : Nat} {left right : Nat → Nat} {changed : Finset.{0} Nat}
  (R : Erdos390.WholePaper.BankPaperRealization n (Erdos390.WholePaper.upperEndpoint n h))
  (certificate : Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n left right changed) (deltaStar : Real)
  (selector : Nat → Real),
  (∀ (label : Nat),
      Membership.mem.{0, 0}
          (Erdos390.WholePaper.completeRoughLabelSet (Erdos390.Full.ArithmeticModel.yNat n)
            (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet R certificate deltaStar K))
          label →
        Erdos390.WholePaper.BankPaperRealization.RoughCanonicalActiveNonexceptionalLabel n deltaStar label →
          Eq.{1}
            (∑ a ∈ Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedRow R certificate deltaStar K label,
              selector a)
            (Erdos390.WholePaper.BankPaperRealization.roughCanonicalPostchargeRowTarget R deltaStar label)) →
    (∀ (label : Nat),
        Membership.mem.{0, 0}
            (Erdos390.WholePaper.completeRoughLabelSet (Erdos390.Full.ArithmeticModel.yNat n)
              (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet R certificate deltaStar K))
            label →
          Ne.{1} label (1 : Nat) →
            Erdos390.WholePaper.BankPaperRealization.RoughCanonicalExceptionalLabel n deltaStar label →
              Eq.{1}
                (∑
                  a ∈ Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedRow R certificate deltaStar K label,
                  selector a)
                (0 : Real)) →
      (∀ (label : Nat),
          Erdos390.WholePaper.IsCompleteRoughLabel (Erdos390.Full.ArithmeticModel.yNat n) label →
            Erdos390.WholePaper.BankPaperRealization.RoughCanonicalActiveNonexceptionalLabel n deltaStar label →
              Erdos390.WholePaper.BankPaperRealization.RoughCanonicalPostchargeRowCapacity R certificate deltaStar K
                label) →
        Eq.{1}
          (HSub.hSub.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0}
                ↑(Finset.card.{0} (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar))
                ↑(Finset.card.{0} (Erdos390.WholePaper.BankPaperRealization.prechargeBaseState R)))
              (∑
                a ∈
                  Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet R certificate deltaStar K,
                selector a))
            ↑h)
          (Neg.neg.{0}
            (Erdos390.WholePaper.BankPaperRealization.roughCanonicalPostchargeRowDiscrepancy R certificate deltaStar K
              (1 : Nat) selector)) := by sorry
