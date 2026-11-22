-- Prove2me | Theorems.Thm_Erdos390_Full_FiniteProbability_sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
-- name    : Erdos390.Full.FiniteProbability.sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:02:22.212557+00:00
-- url     : https://prove2.me/theorems/1778f214-e22b-4ab0-a807-0b45b231d29c
-- title:
--   Mixture covariance stability from component covariance rows
-- statement:
--   Let two tagged mixtures use the same finite component weights, with laws $\mu_c,\nu_c$ and respective observables $F,H_i$ on possibly different finite spaces. Suppose $A_F,A_H,d_F\ge0$ and, in every component, $|\mathbb E_\mu F|\le A_F$, $\sum_i|\mathbb E_\mu H_i|\le A_H$, $|\mathbb E_\nu F-\mathbb E_\mu F|\le d_F$, and $\sum_i|\mathbb E_\nu H_i-\mathbb E_\mu H_i|\le d_H$. Instead assume $\sum_i|\operatorname{Cov}_{\nu_c}(F,H_i)-\operatorname{Cov}_{\mu_c}(F,H_i)|\le d_{\rm Cov}$ in every component. Then
--
--   $$\sum_i|\operatorname{Cov}_\nu(F,H_i)-\operatorname{Cov}_\mu(F,H_i)|\le d_{\rm Cov}+2((A_F+d_F)d_H+A_Hd_F).$$
--
--   The doubled loss accounts for both component mean products and the covariance between component means.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/FiniteProbabilityMixturePerturbation.lean#L284-L412

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

universe u_1 u_2 u_3 u_4

theorem Erdos390.Full.FiniteProbability.sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance :
∀ {Cell : Type u_1} {I : Type u_2} [inst : Fintype.{u_1} Cell] [inst_1 : Fintype.{u_2} I] {Omega : Cell → Type u_3}
  {Theta : Cell → Type u_4} [inst_2 : (c : Cell) → Fintype.{u_3} (Omega c)]
  [inst_3 : (c : Cell) → Fintype.{u_4} (Theta c)] (weight : Erdos390.Full.FiniteProbability.{u_1} Cell)
  (mu : (c : Cell) → Erdos390.Full.FiniteProbability.{u_3} (Omega c))
  (nu : (c : Cell) → Erdos390.Full.FiniteProbability.{u_4} (Theta c)) (Fmu : (c : Cell) → Omega c → Real)
  (Fnu : (c : Cell) → Theta c → Real) (Hmu : (c : Cell) → I → Omega c → Real) (Hnu : (c : Cell) → I → Theta c → Real)
  {AF AH dF dH dCov : Real},
  LE.le.{0} (0 : Real) AF →
    LE.le.{0} (0 : Real) AH →
      LE.le.{0} (0 : Real) dF →
        (∀ (c : Cell), LE.le.{0} (abs.{0} (Erdos390.Full.FiniteProbability.expect.{u_3} (mu c) (Fmu c))) AF) →
          (∀ (c : Cell), LE.le.{0} (∑ i, abs.{0} (Erdos390.Full.FiniteProbability.expect.{u_3} (mu c) (Hmu c i))) AH) →
            (∀ (c : Cell),
                LE.le.{0}
                  (abs.{0}
                    (HSub.hSub.{0, 0, 0} (Erdos390.Full.FiniteProbability.expect.{u_4} (nu c) (Fnu c))
                      (Erdos390.Full.FiniteProbability.expect.{u_3} (mu c) (Fmu c))))
                  dF) →
              (∀ (c : Cell),
                  LE.le.{0}
                    (∑ i,
                      abs.{0}
                        (HSub.hSub.{0, 0, 0} (Erdos390.Full.FiniteProbability.expect.{u_4} (nu c) (Hnu c i))
                          (Erdos390.Full.FiniteProbability.expect.{u_3} (mu c) (Hmu c i))))
                    dH) →
                (∀ (c : Cell),
                    LE.le.{0}
                      (∑ i,
                        abs.{0}
                          (HSub.hSub.{0, 0, 0}
                            (Erdos390.Full.FiniteProbability.covariance.{u_4} (nu c) (Fnu c) (Hnu c i))
                            (Erdos390.Full.FiniteProbability.covariance.{u_3} (mu c) (Fmu c) (Hmu c i))))
                      dCov) →
                  LE.le.{0}
                    (∑ i,
                      abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.FiniteProbability.covariance.{max u_1 u_4}
                            (Erdos390.Full.FiniteProbability.sigmaMixture.{u_1, u_4} weight nu)
                            (fun x => Fnu (Sigma.fst.{u_1, u_4} x) (Sigma.snd.{u_1, u_4} x)) fun x =>
                            Hnu (Sigma.fst.{u_1, u_4} x) i (Sigma.snd.{u_1, u_4} x))
                          (Erdos390.Full.FiniteProbability.covariance.{max u_1 u_3}
                            (Erdos390.Full.FiniteProbability.sigmaMixture.{u_1, u_3} weight mu)
                            (fun x => Fmu (Sigma.fst.{u_1, u_3} x) (Sigma.snd.{u_1, u_3} x)) fun x =>
                            Hmu (Sigma.fst.{u_1, u_3} x) i (Sigma.snd.{u_1, u_3} x))))
                    (HAdd.hAdd.{0, 0, 0} dCov
                      (HMul.hMul.{0, 0, 0} (2 : Real)
                        (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} AF dF) dH)
                          (HMul.hMul.{0, 0, 0} AH dF)))) := by sorry
