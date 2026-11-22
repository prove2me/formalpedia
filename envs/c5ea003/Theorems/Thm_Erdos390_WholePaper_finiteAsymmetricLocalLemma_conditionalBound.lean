-- Prove2me | Theorems.Thm_Erdos390_WholePaper_finiteAsymmetricLocalLemma_conditionalBound
-- name    : Erdos390.WholePaper.finiteAsymmetricLocalLemma_conditionalBound
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:17:53.28796+00:00
-- url     : https://prove2.me/theorems/063cdcd8-1fb8-49d4-b577-9feadf22e41c
-- title:
--   Division-free conditional estimate for the asymmetric local lemma
-- statement:
--   Let $(\Omega,\mu)$ be a probability space, $I$ a finite index set, and $A_i$ measurable events. Let $\Gamma(i)\subset I$ and $0\le x_i<1$. Write $E_S=\bigcap_{j\in S}A_j^c$. Assume $\mu(A_i\cap E_S)=\mu(A_i)\mu(E_S)$ whenever $i\notin S$ and $S\cap\Gamma(i)=\varnothing$, and assume $\mu(A_i)\le x_i\prod_{j\in\Gamma(i)}(1-x_j)$. Then for every $S\subset I$ and $i\notin S$,
--   $$\mu(A_i\cap E_S)\le x_i\mu(E_S).$$
--   The estimate avoids division, and therefore makes sense before positivity of the conditioning event has been established.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/FiniteAsymmetricLocalLemma.lean#L74-L305

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_007

universe u_1 u_2

theorem Erdos390.WholePaper.finiteAsymmetricLocalLemma_conditionalBound :
∀ {I : Type u_1} {Omega : Type u_2} [Fintype.{u_1} I] [DecidableEq.{u_1 + 1} I] [inst : MeasurableSpace.{u_2} Omega]
  (mu : MeasureTheory.Measure.{u_2} Omega) [MeasureTheory.IsProbabilityMeasure.{u_2} mu] (A : I → Set.{u_2} Omega)
  (Gamma : I → Finset.{u_1} I) (x : I → Real),
  (∀ (i : I), MeasurableSet.{u_2} (A i)) →
    (∀ (i : I), And (LE.le.{0} (0 : Real) (x i)) (LT.lt.{0} (x i) (1 : Real))) →
      (∀ (i : I) (s : Finset.{u_1} I),
          i ∉ s →
            Disjoint.{u_1} s (Gamma i) →
              Eq.{1}
                (MeasureTheory.Measure.real.{u_2} mu
                  (Inter.inter.{u_2} (A i) (Erdos390.WholePaper.avoidEvents.{u_1, u_2} A s)))
                (HMul.hMul.{0, 0, 0} (MeasureTheory.Measure.real.{u_2} mu (A i))
                  (MeasureTheory.Measure.real.{u_2} mu (Erdos390.WholePaper.avoidEvents.{u_1, u_2} A s)))) →
        (∀ (i : I),
            LE.le.{0} (MeasureTheory.Measure.real.{u_2} mu (A i))
              (HMul.hMul.{0, 0, 0} (x i) (∏ j ∈ Gamma i, HSub.hSub.{0, 0, 0} (1 : Real) (x j)))) →
          ∀ (s : Finset.{u_1} I),
            ∀ i ∉ s,
              LE.le.{0}
                (MeasureTheory.Measure.real.{u_2} mu
                  (Inter.inter.{u_2} (A i) (Erdos390.WholePaper.avoidEvents.{u_1, u_2} A s)))
                (HMul.hMul.{0, 0, 0} (x i)
                  (MeasureTheory.Measure.real.{u_2} mu (Erdos390.WholePaper.avoidEvents.{u_1, u_2} A s))) := by sorry
