-- Prove2me | Theorems.Thm_Erdos390_WholePaper_bankPaperCanonicalSectionNinePostHeight_headMargins_of_linearBounds
-- name    : Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeight_headMargins_of_linearBounds
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:01:37.704427+00:00
-- url     : https://prove2.me/theorems/40cc726b-3681-48a1-85ce-8bab94cb1f95
-- title:
--   Uniform positive head-simplex margins from linear envelopes
-- statement:
--   Let $P$ be finite, $E\in\mathbb N$ positive, $a_p>0$, $b_p\ge0$, and $c_-,c_+,N,q>0$. Suppose $a_pN\le t_p\le b_pN$, $c_-N\le q\le c_+N$, and $2\sum_pb_p\le Ec_-$. Let $a_*$ be the source positive finite coordinate floor for $a$, and set $m=\min(1/2,a_*/(Ec_+))$. Then
--
--   $$m>0,\qquad m\le\frac{t_p}{Eq}\ (p\in P),\qquad m\le1-\sum_{p\in P}\frac{t_p}{Eq}.$$
--
--   The common margin is independent of N, the target vector, and the active mass q; it also covers the empty head set.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSectionNinePostHeightHeadMarginAlgebra.lean#L125-L251

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_010

theorem Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeight_headMargins_of_linearBounds :
∀ {P : Finset.{0} Nat} (E : Nat),
  LT.lt.{0} (0 : Nat) E →
    ∀ (a b : ↥P → Real) (cLower cUpper N q : Real) (target : ↥P → Real),
      (∀ (p : ↥P), LT.lt.{0} (0 : Real) (a p)) →
        (∀ (p : ↥P), LE.le.{0} (0 : Real) (b p)) →
          LT.lt.{0} (0 : Real) cLower →
            LT.lt.{0} (0 : Real) cUpper →
              LT.lt.{0} (0 : Real) N →
                LT.lt.{0} (0 : Real) q →
                  (∀ (p : ↥P), LE.le.{0} (HMul.hMul.{0, 0, 0} (a p) N) (target p)) →
                    (∀ (p : ↥P), LE.le.{0} (target p) (HMul.hMul.{0, 0, 0} (b p) N)) →
                      LE.le.{0} (HMul.hMul.{0, 0, 0} cLower N) q →
                        LE.le.{0} q (HMul.hMul.{0, 0, 0} cUpper N) →
                          LE.le.{0} (HMul.hMul.{0, 0, 0} (2 : Real) (∑ p, b p)) (HMul.hMul.{0, 0, 0} (↑E) cLower) →
                            have margin :=
                              Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightHeadMargin E a cUpper;
                            And (LT.lt.{0} (0 : Real) margin)
                              (And
                                (∀ (p : ↥P),
                                  LE.le.{0} margin (HDiv.hDiv.{0, 0, 0} (target p) (HMul.hMul.{0, 0, 0} (↑E) q)))
                                (LE.le.{0} margin
                                  (HSub.hSub.{0, 0, 0} (1 : Real)
                                    (∑ p, HDiv.hDiv.{0, 0, 0} (target p) (HMul.hMul.{0, 0, 0} (↑E) q))))) := by sorry
