-- Prove2me | Theorems.Thm_Erdos390_Full_TwoLocalRestorationBound_abs_pairRestoredNumerator_sub_expect_le
-- name    : Erdos390.Full.TwoLocalRestorationBound.abs_pairRestoredNumerator_sub_expect_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:32:06.587186+00:00
-- url     : https://prove2.me/theorems/5dd325d4-06c9-41b7-9868-3db274362a47
-- title:
--   Two-prime restoration numerator bound
-- statement:
--   Let $\nu$ be a finite probability law and $v$ a natural-valued variable. Fix natural $p,q,A_p,A_q,r,s$ and real $\eta_p,\eta_q,L,G$. Suppose $\mathbb E_\nu\mathbf1_{p^uq^b\mid v(\omega)}\le G/(p^uq^b)$ for every pair of natural exponents $u,b$. Write $T_p(r)$ and $T_q(s)$ for the corresponding coefficient tails, and $N_{r,s}$ for the two-local restored numerator.
--
--   $$|N_{r,s}-\mathbb E_\nu\mathbf1_{p^rq^s\mid v(\omega)}|\le G T_p(r)q^{-s}+Gp^{-r}T_q(s)+GT_p(r)T_q(s).$$
--
--   This is the exact finite restoration estimate used before controlling a quotient by its normalizer.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/TwoLocalRestorationBound.lean#L109-L260

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

universe u_1

theorem Erdos390.Full.TwoLocalRestorationBound.abs_pairRestoredNumerator_sub_expect_le :
∀ {Omega : Type u_1} [inst : Fintype.{u_1} Omega] (nu : Erdos390.Full.FiniteProbability.{u_1} Omega)
  (value : Omega → Nat) {p q Ap Aq r s : Nat} {etaP etaQ L G : Real},
  (∀ (u v : Nat),
      LE.le.{0}
        (Erdos390.Full.FiniteProbability.expect.{u_1} nu fun omega =>
          Erdos390.Full.ArithmeticModel.divInd (Erdos390.Full.OmittedTiltPairChamber.pairPower p q u v) (value omega))
        (HDiv.hDiv.{0, 0, 0} G (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑p) u) (HPow.hPow.{0, 0, 0} (↑q) v)))) →
    LE.le.{0}
      (abs.{0}
        (HSub.hSub.{0, 0, 0}
          (Erdos390.Full.TwoLocalRestorationBound.pairRestoredNumerator.{u_1} nu value p q Ap Aq etaP etaQ L r s)
          (Erdos390.Full.FiniteProbability.expect.{u_1} nu fun omega =>
            Erdos390.Full.ArithmeticModel.divInd (Erdos390.Full.OmittedTiltPairChamber.pairPower p q r s)
              (value omega))))
      (Erdos390.Full.TwoLocalRestorationBound.pairRestorationError p q Ap Aq r s etaP etaQ L G) := by sorry
