-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_fourFiveRealEndpointFullyBoundedAssemblyError_le_logCube
-- name    : Erdos390.WholePaper.BankPaperRealization.fourFiveRealEndpointFullyBoundedAssemblyError_le_logCube
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:57:08.350984+00:00
-- url     : https://prove2.me/theorems/9ca8b761-5308-4a35-9c6e-1a07944ff96c
-- title:
--   Fully bounded four/five assembly error on the cubic-logarithmic scale
-- statement:
--   Let $C,M,Z\ge0$ and $y,A,B\in\mathbb N$ with $2\le y$, $A\le B$, and $B\le Z$. Assume $y$ is at least the reciprocal-BV safe cutoff, $1\le\log y\le y$, and the prime-coordinate reciprocal mass up to $B$ is at most $M$. For the source fully bounded real-endpoint assembly error $E(C;y,A,B,M)$ and signed-core assembly constant $C_{\rm asm}(C,M)$,
--
--   $$E(C;y,A,B,M)\le C_{\rm asm}(C,M)\frac Z{(\log y)^3}.$$
--
--   This is a finite conversion of all assembly errors to one explicit scale.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperFourFiveSignedCoreErrorAdapter.lean#L85-L297

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_009

theorem Erdos390.WholePaper.BankPaperRealization.fourFiveRealEndpointFullyBoundedAssemblyError_le_logCube :
∀ {C M Z : Real} {y A B : Nat},
  LE.le.{0} (0 : Real) C →
    LE.le.{0} (0 : Real) M →
      LE.le.{0} (2 : Nat) y →
        LE.le.{0} A B →
          LE.le.{0} Erdos390.WholePaper.BankPaperRealization.fourFiveReciprocalBVSafeCutoff y →
            LE.le.{0} (1 : Real) (Real.log ↑y) →
              LE.le.{0} (Real.log ↑y) ↑y →
                LE.le.{0} (↑B) Z →
                  LE.le.{0} (0 : Real) Z →
                    LE.le.{0} (Erdos390.WholePaper.BankPaperRealization.fourFivePrimeCoordinateReciprocalMass y B) M →
                      LE.le.{0}
                        (Erdos390.WholePaper.BankPaperRealization.fourFiveRealEndpointFullyBoundedAssemblyError C y A B
                          M)
                        (HMul.hMul.{0, 0, 0}
                          (Erdos390.WholePaper.BankPaperRealization.fourFiveSignedCoreAssemblyLogCubeConstant C M)
                          (HDiv.hDiv.{0, 0, 0} Z (HPow.hPow.{0, 0, 0} (Real.log ↑y) (3 : Nat)))) := by sorry
