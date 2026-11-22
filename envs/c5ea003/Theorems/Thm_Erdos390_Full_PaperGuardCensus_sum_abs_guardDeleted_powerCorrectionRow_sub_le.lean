-- Prove2me | Theorems.Thm_Erdos390_Full_PaperGuardCensus_sum_abs_guardDeleted_powerCorrectionRow_sub_le
-- name    : Erdos390.Full.PaperGuardCensus.sum_abs_guardDeleted_powerCorrectionRow_sub_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:20:47.633565+00:00
-- url     : https://prove2.me/theorems/90471d34-7e5e-410c-8994-351de81d5d3d
-- title:
--   Guard deletion perturbs the full power-correction row
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, and $\mathcal P=\{p\text{ prime}:W<p\le Y\}$. For a valuation law $\lambda$, put $\Delta_\lambda(p,q)=\operatorname{Cov}_\lambda(v_p,v_q)-\operatorname{Cov}_\lambda(\mathbf1_{p\mid m},\mathbf1_{q\mid m})$. Write $E_g(K,d)=(K^2+K)(7d+2d^2)$, the guard power-correction row error. Consider nonempty raw cells for a head-pattern family and physical intervals, arbitrary cell scores, and common tagged-mixture weights. Let $\mu_c$ be the tilted cell law and $\nu_c$ its law after deleting the specified guards. Assume $W>1$, $K,d\ge0$, every valuation envelope is at most $K$, every guard mass is less than one, and the exact guard normalization perturbation is at most $d$ in every cell. For each band prime $p$,
--
--   $$\sum_{q\in\mathcal P}|\Delta_\nu(p,q)-\Delta_\mu(p,q)|\le E_g(K,d).$$
--
--   The bound preserves the actual mixture weights and uses the exact conditional-normalization error.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperGuardPowerCorrectionMixture.lean#L48-L225

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

universe u_1

theorem Erdos390.Full.PaperGuardCensus.sum_abs_guardDeleted_powerCorrectionRow_sub_le :
∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] (P : Head → Erdos390.Full.HeadPattern.Pattern)
  (Iphys : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) {n W : Nat},
  LT.lt.{0} (1 : Nat) W →
    ∀ (guardsNat : Finset.{0} Nat)
      (hS :
        ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
          Finset.Nonempty.{0} (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P Iphys n c))
      (score :
        (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) →
          ↥(Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P Iphys n c) → Real)
      (weight : Erdos390.Full.FiniteProbability.{u_1} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head))
      (p : Erdos390.Full.ArithmeticBandGeometry.BandPrime n W) {K d : Real},
      LE.le.{0} (0 : Real) K →
        LE.le.{0} (0 : Real) d →
          (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
              LE.le.{0} (Erdos390.Full.PaperGuardCensus.valuationEnvelope.{u_1} Iphys n W c) K) →
            ∀
              (hsmall :
                ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                  LT.lt.{0}
                    (Erdos390.Full.FiniteProbability.guardMass.{0}
                      (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                        (Erdos390.Full.FiniteProbability.uniformOnFinset.{0}
                          (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P Iphys n c) (hS c))
                        (score c))
                      (Erdos390.Full.GuardedUniformCell.guardSubtype.{0}
                        (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P Iphys n c) guardsNat))
                    (1 : Real)),
              (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                  LE.le.{0}
                    (Erdos390.Full.FiniteProbability.guardPerturbation.{0}
                      (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                        (Erdos390.Full.FiniteProbability.uniformOnFinset.{0}
                          (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P Iphys n c) (hS c))
                        (score c))
                      (Erdos390.Full.GuardedUniformCell.guardSubtype.{0}
                        (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P Iphys n c) guardsNat))
                    d) →
                let S := fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                  Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P Iphys n c;
                let mu := fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                  Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                    (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} (S c) (hS c)) (score c);
                let Gsub := fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                  Erdos390.Full.GuardedUniformCell.guardSubtype.{0} (S c) guardsNat;
                have nu := fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                  Erdos390.Full.FiniteProbability.deleteGuards.{0} (mu c) (Gsub c) (hsmall c);
                have value := fun (x : (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) × ↥(S c)) =>
                  ↑(Sigma.snd.{u_1, 0} x);
                LE.le.{0}
                  (∑ q : Erdos390.Full.ArithmeticBandGeometry.BandPrime n W,
                    abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.PaperGuardCensus.powerCorrectionCovariance.{u_1}
                          (Erdos390.Full.FiniteProbability.sigmaMixture.{u_1, 0} weight nu) value ↑p ↑q)
                        (Erdos390.Full.PaperGuardCensus.powerCorrectionCovariance.{u_1}
                          (Erdos390.Full.FiniteProbability.sigmaMixture.{u_1, 0} weight mu) value ↑p ↑q)))
                  (Erdos390.Full.PaperGuardCensus.guardPowerCorrectionRowError K d) := by sorry
