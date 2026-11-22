-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_fourFiveRightDiscreteBVNorm_cutoffSequence_le_two
-- name    : Erdos390.WholePaper.BankPaperRealization.fourFiveRightDiscreteBVNorm_cutoffSequence_le_two
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:57:48.275189+00:00
-- url     : https://prove2.me/theorems/94fc25d9-c067-4a00-8c9b-7fffdf8dd0cf
-- title:
--   A monotone cutoff sequence has discrete BV norm at most two
-- statement:
--   Let $A\le Y$ and $R$ be natural numbers. Let $g:\mathbb N\to\mathbb R$ be nondecreasing on $[A,Y]\cap\mathbb N$ and satisfy $0\le g(n)\le1$ there. Define $f(n)=g(n)$ when $A<n\le R$, and $f(n)=0$ otherwise. Then
--
--   $$|f(Y)|+\sum_{A<m\le Y-1}|f(m+1)-f(m)|\le2.$$
--
--   The bound controls the bounded variation of a moving-face cutoff without dependence on its location.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperFourFiveMovingFaceBV.lean#L52-L212

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_009

theorem Erdos390.WholePaper.BankPaperRealization.fourFiveRightDiscreteBVNorm_cutoffSequence_le_two :
∀ (g : Nat → Real) {A R Y : Nat},
  LE.le.{0} A Y →
    (∀ (a : Nat),
        Membership.mem.{0, 0} (Finset.Icc.{0} A Y) a →
          ∀ (b : Nat), Membership.mem.{0, 0} (Finset.Icc.{0} A Y) b → LE.le.{0} a b → LE.le.{0} (g a) (g b)) →
      (∀ (n : Nat), Membership.mem.{0, 0} (Finset.Icc.{0} A Y) n → LE.le.{0} (0 : Real) (g n)) →
        (∀ (n : Nat), Membership.mem.{0, 0} (Finset.Icc.{0} A Y) n → LE.le.{0} (g n) (1 : Real)) →
          LE.le.{0}
            (Erdos390.WholePaper.BankPaperRealization.fourFiveRightDiscreteBVNorm
              (Erdos390.WholePaper.BankPaperRealization.fourFiveCutoffSequence A R g) A Y)
            (2 : Real) := by sorry
