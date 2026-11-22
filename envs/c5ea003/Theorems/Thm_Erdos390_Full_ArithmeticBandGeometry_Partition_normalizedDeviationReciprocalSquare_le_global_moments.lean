-- Prove2me | Theorems.Thm_Erdos390_Full_ArithmeticBandGeometry_Partition_normalizedDeviationReciprocalSquare_le_global_moments
-- name    : Erdos390.Full.ArithmeticBandGeometry.Partition.normalizedDeviationReciprocalSquare_le_global_moments
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T14:57:45.799043+00:00
-- url     : https://prove2.me/theorems/69fdc0d1-7c00-4f9f-8fe8-cc7bbe78f8ee
-- title:
--   Local reciprocal-square deviation bounded by global moments
-- statement:
--   For a prime partition P at n>1 and any band i, let H_i=P.mass_i, α_i=P.center_i, and t_p=log(p)/log(y(n)). Its normalized local reciprocal-square deviation D_i obeys the following bound, where both sums on the right are over all band primes. This retains both global moments needed at a moving low center.
--
--   $$D_i:=H_i^{-1}\sum_{p\in i}\frac{|\operatorname{dev}_p|}{p^2}\le H_i^{-1}\left(\alpha_i\sum_p\frac1{p^2}+\sum_p\frac{t_p}{p^2}\right).$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperNonstepLocalDiagonal.lean#L64-L154

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_005

universe u_1

theorem Erdos390.Full.ArithmeticBandGeometry.Partition.normalizedDeviationReciprocalSquare_le_global_moments :
∀ {n W : Nat} {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band]
  (P : Erdos390.Full.ArithmeticBandGeometry.Partition.{u_1} n W Band),
  LT.lt.{0} (1 : Nat) n →
    ∀ (i : Band),
      LE.le.{0} (Erdos390.Full.ArithmeticBandGeometry.Partition.normalizedDeviationReciprocalSquare.{u_1} P i)
        (HMul.hMul.{0, 0, 0}
          (HDiv.hDiv.{0, 0, 0} (1 : Real) (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_1} P i))
          (HAdd.hAdd.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_1} P i)
              (Erdos390.Full.PrimeSums.bandReciprocalSquareSum n W))
            (Erdos390.Full.PrimeSums.bandTReciprocalSquareSum n W))) := by sorry
