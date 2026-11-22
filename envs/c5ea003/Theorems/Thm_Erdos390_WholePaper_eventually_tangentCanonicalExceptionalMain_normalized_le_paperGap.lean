-- Prove2me | Theorems.Thm_Erdos390_WholePaper_eventually_tangentCanonicalExceptionalMain_normalized_le_paperGap
-- name    : Erdos390.WholePaper.eventually_tangentCanonicalExceptionalMain_normalized_le_paperGap
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:06:31.401409+00:00
-- url     : https://prove2.me/theorems/9e56f2fd-6290-42c6-86a5-d04f7c802fd9
-- title:
--   The exceptional sieve main term fits the head-gap budget
-- statement:
--   Let $W\in\mathbb N$, $r_0\in\mathbb R$, and $\delta>0$. Write $g=d_W(2-r_0)$ for the head gap and $C_M$ for the canonical Selberg main constant. Suppose $80C_M\delta<g$. For all sufficiently large $n$, uniformly in natural $K,h,u,v$ with $u>0$, the canonical exceptional length sum $S(n,K,h,X_0,u,v)$ satisfies
--   $$\frac{u}{n}S(n,K,h,X_0(n),u,v)\frac{C_M}{\log y(n)}\le\frac g4,$$
--   where $X_0(n)$ is the paper exceptional cutoff at exponent $\delta$.
--
--   The estimate reserves a fixed part of the candidate head gap for the exceptional main term.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/TangentPaperCleanListAbsorption.lean#L353-L453

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008

theorem Erdos390.WholePaper.eventually_tangentCanonicalExceptionalMain_normalized_le_paperGap :
∀ {W : Nat} {r0 deltaStar : Real},
  LT.lt.{0} (0 : Real) deltaStar →
    LT.lt.{0}
        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (80 : Real) Erdos390.WholePaper.tangentSelbergCanonicalMainConstant)
          deltaStar)
        (Erdos390.WholePaper.tangentPaperHeadGap W r0) →
      ∀ᶠ (n : Nat) in Filter.atTop.{0},
        ∀ (K h u v : Nat),
          LT.lt.{0} (0 : Nat) u →
            LE.le.{0}
              (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} ↑u ↑n)
                (HMul.hMul.{0, 0, 0}
                  (Erdos390.WholePaper.tangentCanonicalExceptionalLengthSum n K h
                    (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n) u v)
                  (HDiv.hDiv.{0, 0, 0} Erdos390.WholePaper.tangentSelbergCanonicalMainConstant
                    (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)))))
              (HDiv.hDiv.{0, 0, 0} (Erdos390.WholePaper.tangentPaperHeadGap W r0) (4 : Real)) := by sorry
