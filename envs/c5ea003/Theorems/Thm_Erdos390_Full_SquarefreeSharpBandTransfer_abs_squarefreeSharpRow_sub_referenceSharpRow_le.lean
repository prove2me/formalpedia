-- Prove2me | Theorems.Thm_Erdos390_Full_SquarefreeSharpBandTransfer_abs_squarefreeSharpRow_sub_referenceSharpRow_le
-- name    : Erdos390.Full.SquarefreeSharpBandTransfer.abs_squarefreeSharpRow_sub_referenceSharpRow_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:32:04.125314+00:00
-- url     : https://prove2.me/theorems/141d989d-7303-4698-8794-c2fc94ca79cf
-- title:
--   Entrywise squarefree errors aggregate in the sharp band rows
-- statement:
--   Let a bounded valuation law and a partition of the moving prime band be given, with $n,W>1$, positive harmonic masses $m_i$, and band centers $c_i$. Assume $C_d\ge0$ and, for band primes $p,q$,
--   $$|\operatorname{Cov}(I_p,I_q)-R_{pq}|\le\frac{\epsilon_o}{pq}+1_{p=q}\left(\frac{\epsilon_d}{p}+\frac{C_d}{p^2}\right),$$
--   where $R$ is the squarefree Dickman reference matrix. For every band vector $v$ with $|v_j|\le1$ and every band $i$,
--   $$|\operatorname{SquarefreeSharpRow}(v)_i-\operatorname{ReferenceSharpRow}(v)_i|\le\epsilon_o\frac{\sum_p t_p/p}{c_i}+\epsilon_d+\frac{C_d}{W}.$$
--   This retains the actual center of the row and introduces no factor depending on the number of bands. The moving prime band is $\{p\text{ prime}:W<p\le\lfloor n^{2/9}\rfloor\}$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/SquarefreeSharpBandTransfer.lean#L54-L357

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

universe u_1 u_2

theorem Erdos390.Full.SquarefreeSharpBandTransfer.abs_squarefreeSharpRow_sub_referenceSharpRow_le :
∀ {Omega : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Omega] [inst_1 : Fintype.{u_2} Band]
  [inst_2 : DecidableEq.{u_2 + 1} Band] {M n W : Nat}
  (law : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_1} Omega M)
  (P : Erdos390.Full.ArithmeticBandGeometry.Partition.{u_2} n W Band),
  LT.lt.{0} (1 : Nat) n →
    LT.lt.{0} (1 : Nat) W →
      ∀ {epsilonOff epsilonDiag Cdiag : Real},
        LE.le.{0} (0 : Real) Cdiag →
          (∀ (p q : Erdos390.Full.ArithmeticBandGeometry.BandPrime n W),
              LE.le.{0}
                (abs.{0}
                  (HSub.hSub.{0, 0, 0} (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1} law ↑p ↑q)
                    (Erdos390.Full.SquarefreeCovarianceReference.squarefreeReferenceEntry n ↑p ↑q)))
                (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} epsilonOff (HMul.hMul.{0, 0, 0} ↑↑p ↑↑q))
                  (ite.{1} (Eq.{1} p q)
                    (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} epsilonDiag ↑↑p)
                      (HDiv.hDiv.{0, 0, 0} Cdiag (HPow.hPow.{0, 0, 0} ↑↑p (2 : Nat))))
                    (0 : Real)))) →
            ∀ (q : Band → Real),
              (∀ (j : Band), LE.le.{0} (abs.{0} (q j)) (1 : Real)) →
                ∀ (i : Band),
                  LE.le.{0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.SquarefreeSharpBandTransfer.squarefreeSharpRow.{u_1, u_2} law P q i)
                        (Erdos390.Full.SquarefreeSharpBandTransfer.referenceSharpRow.{u_2} P q i)))
                    (HAdd.hAdd.{0, 0, 0}
                      (HAdd.hAdd.{0, 0, 0}
                        (HDiv.hDiv.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} epsilonOff (Erdos390.Full.PrimeSums.bandTReciprocalSum n W))
                          (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2} P i))
                        epsilonDiag)
                      (HMul.hMul.{0, 0, 0} Cdiag (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑W))) := by sorry
