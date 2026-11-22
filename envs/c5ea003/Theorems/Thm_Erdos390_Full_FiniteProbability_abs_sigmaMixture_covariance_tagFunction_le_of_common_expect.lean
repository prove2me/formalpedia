-- Prove2me | Theorems.Thm_Erdos390_Full_FiniteProbability_abs_sigmaMixture_covariance_tagFunction_le_of_common_expect
-- name    : Erdos390.Full.FiniteProbability.abs_sigmaMixture_covariance_tagFunction_le_of_common_expect
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T14:54:09.378971+00:00
-- url     : https://prove2.me/theorems/6c60c929-4171-4608-942e-a00bf9537110
-- title:
--   A common component mean bounds covariance with a cell tag
-- statement:
--   Let $w$ be a probability law on a finite cell set and $\mu_c$ finite probability laws on the corresponding component spaces. For a statistic $F$ on their disjoint union and a cell function $H$, assume $|H(c)|\le K$ with $K\ge0$, and $|\mathbb E_{\mu_c}F-m|\le e$ for a common real $m$ and $e\ge0$. Then the tagged mixture satisfies
--   $$|\operatorname{Cov}_{\mu_{\rm mix}}(F,H(c))|\le2Ke.$$
--   This controls the complete mixture covariance, including variation between cells.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/FiniteProbabilityCellConstantCovariance.lean#L22-L149

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

universe u_1 u_2

theorem Erdos390.Full.FiniteProbability.abs_sigmaMixture_covariance_tagFunction_le_of_common_expect :
∀ {Cell : Type u_1} [inst : Fintype.{u_1} Cell] {Omega : Cell → Type u_2}
  [inst_1 : (c : Cell) → Fintype.{u_2} (Omega c)] (weight : Erdos390.Full.FiniteProbability.{u_1} Cell)
  (mu : (c : Cell) → Erdos390.Full.FiniteProbability.{u_2} (Omega c)) (F : Sigma.{u_1, u_2} Omega → Real)
  (H : Cell → Real) (main error K : Real),
  LE.le.{0} (0 : Real) error →
    LE.le.{0} (0 : Real) K →
      (∀ (c : Cell), LE.le.{0} (abs.{0} (H c)) K) →
        (∀ (c : Cell),
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.FiniteProbability.expect.{u_2} (mu c) fun x => F (Sigma.mk.{u_1, u_2} c x)) main))
              error) →
          LE.le.{0}
            (abs.{0}
              (Erdos390.Full.FiniteProbability.covariance.{max u_1 u_2}
                (Erdos390.Full.FiniteProbability.sigmaMixture.{u_1, u_2} weight mu) F fun x =>
                H (Sigma.fst.{u_1, u_2} x)))
            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) K) error) := by sorry
