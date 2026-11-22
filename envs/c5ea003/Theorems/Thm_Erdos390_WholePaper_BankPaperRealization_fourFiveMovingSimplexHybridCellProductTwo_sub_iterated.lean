-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_fourFiveMovingSimplexHybridCellProductTwo_sub_iterated
-- name    : Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexHybridCellProductTwo_sub_iterated
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:53:38.73136+00:00
-- url     : https://prove2.me/theorems/002f9577-7e60-40f1-96aa-cbba25567db5
-- title:
--   The hybrid-to-iterated simplex cell difference is the integrated face defect
-- statement:
--   Let $A,Y,y$ be natural numbers with $2\le y\le A$ and $u\in\mathbb R$. Put $\lambda(x)=1/(x\log x)$, $a_q=\int_{q-1}^{q}\lambda(z)\,dz$, and $K(x,z)$ equal to its real two-variable moving-simplex kernel. The hybrid expression samples the second variable at $q$ with weight $a_q$, whereas the iterated expression integrates both cell variables. Their exact difference is
--   $$H-I=\sum_{A<p\le Y}\int_{p-1}^p\lambda(x)\,D\!\left(\frac{\log x}{\log y}\right)\,dx,$$
--   where $D(c)$ is the sum over $A<q\le Y$ of the signed Lebesgue cell defects for the conditional moving face at coordinate $c$. Equivalently, its $q$-summand is the right-endpoint approximation $a_qK(x,q)$ minus $\int_{q-1}^q\lambda(z)K(x,z)\,dz$. This exposes the second-coordinate discretization error without discarding its sign.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperFourFiveMovingSimplexCellIdentification.lean#L409-L604

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_009

theorem Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexHybridCellProductTwo_sub_iterated :
∀ {A Y y : Nat} {u : Real},
  LE.le.{0} (2 : Nat) y →
    LE.le.{0} y A →
      Eq.{1}
        (HSub.hSub.{0, 0, 0}
          (Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexHybridCellProductTwo A Y y u)
          (Erdos390.WholePaper.BankPaperRealization.fourFiveMovingSimplexIteratedRealCellProductTwo A Y y u))
        (∑ p ∈ Finset.Ioc.{0} A Y,
          ∫ (x : Real) in ↑(HSub.hSub.{0, 0, 0} p (1 : Nat))..↑p,
            HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.BankPaperRealization.fourFiveLogLogLebesgueDensity x)
              (Erdos390.WholePaper.BankPaperRealization.fourFiveMovingFaceLebesgueCellDefectSum A Y y u
                (Erdos390.WholePaper.BankPaperRealization.fourFiveRealLogCoordinate y x))) := by sorry
