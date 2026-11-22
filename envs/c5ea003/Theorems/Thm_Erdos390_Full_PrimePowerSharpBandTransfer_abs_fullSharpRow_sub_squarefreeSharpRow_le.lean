-- Prove2me | Theorems.Thm_Erdos390_Full_PrimePowerSharpBandTransfer_abs_fullSharpRow_sub_squarefreeSharpRow_le
-- name    : Erdos390.Full.PrimePowerSharpBandTransfer.abs_fullSharpRow_sub_squarefreeSharpRow_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:24:22.694522+00:00
-- url     : https://prove2.me/theorems/98110ee4-565c-4bd7-bd35-ab85fd83c9ae
-- title:
--   Prime-power corrections are small in the sharp band rows
-- statement:
--   Let a bounded valuation law satisfy the five prime-power transfer bounds with constants $C_{\rm pow},\epsilon\ge0$. Let $P$ be a partition of its moving prime band, $n,W>1$, with centers $c_i$. For any real band vector $v$ with $|v_j|\le1$ and any band $i$, put $H_t=\sum_{p\in\mathcal P_{n,W}}t_p/p$. Then
--   $$|\operatorname{FullSharpRow}(v)_i-\operatorname{SquarefreeSharpRow}(v)_i|\le\frac{3C_{\rm pow}(H_t+1)}W+\frac{3\epsilon}W\left(\frac{H_t}{c_i}+1\right).$$
--   The main constant is not divided by the moving-low band center; only the vanishing error carries that loss. The moving prime band is $\{p\text{ prime}:W<p\le\lfloor n^{2/9}\rfloor\}$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PrimePowerSharpBandTransfer.lean#L111-L638

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

theorem Erdos390.Full.PrimePowerSharpBandTransfer.abs_fullSharpRow_sub_squarefreeSharpRow_le :
∀ {Omega : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Omega] [inst_1 : Fintype.{u_2} Band]
  [inst_2 : DecidableEq.{u_2 + 1} Band] {M n W : Nat}
  (law : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_1} Omega M)
  (P : Erdos390.Full.ArithmeticBandGeometry.Partition.{u_2} n W Band),
  LT.lt.{0} (1 : Nat) n →
    LT.lt.{0} (1 : Nat) W →
      ∀ {Cpow epsilon : Real},
        LE.le.{0} (0 : Real) Cpow →
          LE.le.{0} (0 : Real) epsilon →
            Erdos390.Full.PaperPrimePowerLemma75.PrimePowerTransferBounds.{u_1} law n W Cpow epsilon →
              ∀ (q : Band → Real),
                (∀ (j : Band), LE.le.{0} (abs.{0} (q j)) (1 : Real)) →
                  ∀ (i : Band),
                    LE.le.{0}
                      (abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.PrimePowerSharpBandTransfer.fullSharpRow.{u_1, u_2} law P q i)
                          (Erdos390.Full.SquarefreeSharpBandTransfer.squarefreeSharpRow.{u_1, u_2} law P q i)))
                      (HAdd.hAdd.{0, 0, 0}
                        (HMul.hMul.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (3 : Real) Cpow)
                            (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.PrimeSums.bandTReciprocalSum n W) (1 : Real)))
                          (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑W))
                        (HMul.hMul.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (3 : Real) epsilon)
                            (HAdd.hAdd.{0, 0, 0}
                              (HDiv.hDiv.{0, 0, 0} (Erdos390.Full.PrimeSums.bandTReciprocalSum n W)
                                (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2} P i))
                              (1 : Real)))
                          (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑W))) := by sorry
