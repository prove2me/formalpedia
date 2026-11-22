-- Prove2me | Theorems.Thm_Erdos390_Full_FiniteManyLowRawGraphInverse_ordinary_raw_bound
-- name    : Erdos390.Full.FiniteManyLowRawGraphInverse.ordinary_raw_bound
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:02:12.80738+00:00
-- url     : https://prove2.me/theorems/e15f629e-574a-4668-804e-6d6c1f37a8e3
-- title:
--   Ordinary raw inverse estimate with many low coordinates
-- statement:
--   Let Low and High be finite, with High nonempty. Let L be the graph operator of edge weights E, and let q satisfy the weighted gauge ∑ω_xq_x=0. Assume high edges dominate κα_j for an anchor of total mass A>0, κ>0; to avoid conflating the anchor with coordinate scaling, denote coordinate scales by s_x. On high coordinates assume 0<a_min≤s_i≤a_max, nonnegative ω_i with positive sum, and |s_x(Lq)_x|≤G, G≥0. Put B=‖sq‖∞ and b₀=C_low G+ε_low B. Suppose |s_lq_l|≤b₀, high-to-low row magnitudes are at most cross·B/a_min+incoming·b₀, and the low gauge sum has magnitude at most gaugeRatio·(∑high ω_i)b₀. All displayed error coefficients except gaugeRatio are nonnegative. If E₀≤1/2 as defined below, the ordinary inverse bound follows. This is the deterministic maximum-principle absorption step.
--
--   $$\begin{gathered}C_0=\max\{C_{\rm low},a_{\max}[2(\kappa A)^{-1}(a_{\min}^{-1}+{\rm incoming}\,C_{\rm low})+{\rm gaugeRatio}\,C_{\rm low}]\},\\ E_0=\max\{\varepsilon_{\rm low},a_{\max}[2(\kappa A)^{-1}({\rm cross}/a_{\min}+{\rm incoming}\,\varepsilon_{\rm low})+{\rm gaugeRatio}\,\varepsilon_{\rm low}]\},\\ |s_xq_x|\le 2C_0G.\end{gathered}$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/FiniteManyLowRawGraphInverse.lean#L43-L290

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

universe u_1 u_2

theorem Erdos390.Full.FiniteManyLowRawGraphInverse.ordinary_raw_bound :
∀ {Low : Type u_1} {High : Type u_2} [inst : Fintype.{u_1} Low] [inst_1 : Fintype.{u_2} High] [Nonempty.{u_2 + 1} High]
  (edge : Sum.{u_1, u_2} Low High → Sum.{u_1, u_2} Low High → Real) (anchor : High → Real)
  (omega alpha q : Sum.{u_1, u_2} Low High → Real)
  {kappa anchorMass amin amax cross incoming gaugeRatio Clow epsLow G : Real},
  LE.le.{0} (0 : Real) G →
    LT.lt.{0} (0 : Real) kappa →
      Eq.{1} (∑ j, anchor j) anchorMass →
        LT.lt.{0} (0 : Real) anchorMass →
          (∀ (i j : High),
              LE.le.{0} (HMul.hMul.{0, 0, 0} kappa (anchor j))
                (Erdos390.Full.FiniteManyLowRawGraphInverse.highEdge.{u_1, u_2} edge i j)) →
            (∀ (i : High), LE.le.{0} amin (alpha (Sum.inr.{u_1, u_2} i))) →
              LT.lt.{0} (0 : Real) amin →
                (∀ (i : High), LE.le.{0} (alpha (Sum.inr.{u_1, u_2} i)) amax) →
                  (∀ (i : High), LE.le.{0} (0 : Real) (alpha (Sum.inr.{u_1, u_2} i))) →
                    LE.le.{0} (0 : Real) amax →
                      LE.le.{0} (0 : Real) cross →
                        LE.le.{0} (0 : Real) incoming →
                          LE.le.{0} (0 : Real) Clow →
                            LE.le.{0} (0 : Real) epsLow →
                              (∀ (i : High), LE.le.{0} (0 : Real) (omega (Sum.inr.{u_1, u_2} i))) →
                                LT.lt.{0} (0 : Real) (∑ i, omega (Sum.inr.{u_1, u_2} i)) →
                                  Eq.{1} (∑ x, HMul.hMul.{0, 0, 0} (omega x) (q x)) (0 : Real) →
                                    (∀ (x : Sum.{u_1, u_2} Low High),
                                        LE.le.{0}
                                          (abs.{0}
                                            (HMul.hMul.{0, 0, 0} (alpha x)
                                              (Erdos390.Full.FiniteGraphQuotientInverse.graphOperator.{max u_1 u_2} edge
                                                q x)))
                                          G) →
                                      (∀ (l : Low),
                                          LE.le.{0}
                                            (abs.{0}
                                              (HMul.hMul.{0, 0, 0} (alpha (Sum.inl.{u_1, u_2} l))
                                                (q (Sum.inl.{u_1, u_2} l))))
                                            (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} Clow G)
                                              (HMul.hMul.{0, 0, 0} epsLow
                                                (Norm.norm.{max u_1 u_2} fun x =>
                                                  HMul.hMul.{0, 0, 0} (alpha x) (q x))))) →
                                        (∀ (i : High),
                                            LE.le.{0}
                                              (abs.{0}
                                                (∑ l,
                                                  HMul.hMul.{0, 0, 0}
                                                    (edge (Sum.inr.{u_1, u_2} i) (Sum.inl.{u_1, u_2} l))
                                                    (HSub.hSub.{0, 0, 0} (q (Sum.inr.{u_1, u_2} i))
                                                      (q (Sum.inl.{u_1, u_2} l)))))
                                              (HAdd.hAdd.{0, 0, 0}
                                                (HDiv.hDiv.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0} cross
                                                    (Norm.norm.{max u_1 u_2} fun x =>
                                                      HMul.hMul.{0, 0, 0} (alpha x) (q x)))
                                                  amin)
                                                (HMul.hMul.{0, 0, 0} incoming
                                                  (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} Clow G)
                                                    (HMul.hMul.{0, 0, 0} epsLow
                                                      (Norm.norm.{max u_1 u_2} fun x =>
                                                        HMul.hMul.{0, 0, 0} (alpha x) (q x))))))) →
                                          LE.le.{0}
                                              (abs.{0}
                                                (∑ l,
                                                  HMul.hMul.{0, 0, 0} (omega (Sum.inl.{u_1, u_2} l))
                                                    (q (Sum.inl.{u_1, u_2} l))))
                                              (HMul.hMul.{0, 0, 0}
                                                (HMul.hMul.{0, 0, 0} gaugeRatio (∑ i, omega (Sum.inr.{u_1, u_2} i)))
                                                (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} Clow G)
                                                  (HMul.hMul.{0, 0, 0} epsLow
                                                    (Norm.norm.{max u_1 u_2} fun x =>
                                                      HMul.hMul.{0, 0, 0} (alpha x) (q x))))) →
                                            LE.le.{0}
                                                (Max.max.{0} epsLow
                                                  (HMul.hMul.{0, 0, 0} amax
                                                    (HAdd.hAdd.{0, 0, 0}
                                                      (HMul.hMul.{0, 0, 0}
                                                        (HMul.hMul.{0, 0, 0} (2 : Real)
                                                          (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                            (HMul.hMul.{0, 0, 0} kappa anchorMass)))
                                                        (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} cross amin)
                                                          (HMul.hMul.{0, 0, 0} incoming epsLow)))
                                                      (HMul.hMul.{0, 0, 0} gaugeRatio epsLow))))
                                                (1 / 2 : Real) →
                                              ∀ (x : Sum.{u_1, u_2} Low High),
                                                LE.le.{0} (abs.{0} (HMul.hMul.{0, 0, 0} (alpha x) (q x)))
                                                  (HMul.hMul.{0, 0, 0}
                                                    (HMul.hMul.{0, 0, 0} (2 : Real)
                                                      (Max.max.{0} Clow
                                                        (HMul.hMul.{0, 0, 0} amax
                                                          (HAdd.hAdd.{0, 0, 0}
                                                            (HMul.hMul.{0, 0, 0}
                                                              (HMul.hMul.{0, 0, 0} (2 : Real)
                                                                (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                  (HMul.hMul.{0, 0, 0} kappa anchorMass)))
                                                              (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) amin)
                                                                (HMul.hMul.{0, 0, 0} incoming Clow)))
                                                            (HMul.hMul.{0, 0, 0} gaugeRatio Clow)))))
                                                    G) := by sorry
