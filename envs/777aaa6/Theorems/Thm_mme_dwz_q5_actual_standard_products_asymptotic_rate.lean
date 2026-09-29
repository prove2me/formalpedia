-- Prove2me | Theorems.Thm_mme_dwz_q5_actual_standard_products_asymptotic_rate
-- name    : mme_dwz_q5_actual_standard_products_asymptotic_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-18T14:10:47.705356+00:00
-- url     : https://prove2.me/theorems/31cd7e74-cbde-4d5c-ba75-f1c09389bd3c
-- title:
--   Actual asymptotic standard-product extraction for the unchanged q=5 DWZ data
-- statement:
--   Use the unchanged exact rational-replay $q=5$ fourth-power data and its synchronized raw parent Z profiles. For each of the 45 supported coarse cells $c=(i_c,j_c,k_c)$, let $p_c$ be its prescribed Z-split profile and let $m_c(t)$ be the denominator-cleared multiplicity. Write
--   $$
--   n_c(t)=\operatorname{length}(p_c,m_c(t)),\qquad N(t)=\sum_c n_c(t),\qquad
--   P_t=\bigotimes_c\operatorname{PrescribedZPower}
--   \bigl(T_{i_cj_ck_c},p_c,m_c(t)\bigr).
--   $$
--   Here $T_{ijk}$ is the literal balanced fourth-power Coppersmith–Winograd constituent at $q=5$. The prescribed projection uses its canonical Z basis and the grade of the left square factor, exactly as in the finite extraction theorem; it is not an unspecified isomorphic tensor.
--
--   Let $H_T$ be the exact target-word logarithmic rate, let $H_X,H_Y$ be the marginal entropies, and let $L_Z$ be the exact two-stage compatible-owner logarithmic rate defined by the shared data. Set
--   $$
--   U=\frac{2830114015881672025944380699373}{10^{30}},
--   \qquad
--   R=H_T-\max\{0,U-H_X,U-H_Y,L_Z\}.
--   $$
--   All logarithms are natural. For every field $K$ and every real $\rho$ satisfying $0\le\rho<R$, every sufficiently large integer $t$ admits an integer $r$ such that
--   $$
--   r\ge\exp(\rho N(t))
--   \quad\text{and}\quad
--   \bigoplus_{j=1}^{r}P_t\;\preceq\;
--   CW_5^{\otimes 4N(t)}.
--   $$
--   The symbol $\preceq$ denotes an actual modewise linear tensor restriction, with the displayed direct sum as target and the CW power as source. The lengths are cofinal: $N(t)=N(1)t$ and $N(1)>0$.
--
--   There are no assumed degree, compatibility, prime, progression-free-set, numeric-budget, or tensor-realization hypotheses. The proof supplies those ingredients from the accepted exact counting, entropy, and finite restriction results. The rate is per fourth-power block, hence the source contains $4N(t)$ atomic CW factors. This theorem alone does not certify that $R$ is positive, supply the component tensor-value lower bounds, or prove the final matrix-multiplication exponent; the interval $0\le\rho<R$ is an explicit rate condition.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5 , Sections 3.7–3.10 and 6.2. Derived exact-data finite-to-asymptotic extraction, using the published q5_global_asymptotic_data, actual numeric-budget tensor restriction, target-count log rate, full ambient entropy ceiling, actual fine-Z compatibility log rate, and prime half-range Salem–Spencer theorem. The raw parent profiles and rational-replay outer distribution are unchanged.

import Definitions.Def_mme_dwz_q5_global_asymptotic_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_CW_2376_address_block
import Mathlib.Topology.Algebra.Order.Field

open Filter MME MME.TensorObj MME.StothersFourth
  MME.DWZRestrictedValue MME.CompleteSplit.CWFourth
  MME.DWZQ5ExactData MME.DWZFourthGlobalWitness MME.DWZQ5AsymptoticData
open scoped Classical Topology
universe u
set_option autoImplicit false

theorem mme_dwz_q5_actual_standard_products_asymptotic_rate {K : Type u} [Field K]
    (rho : ℝ) (hrho : 0 ≤ rho) (hgap : rho < extractionRate) :
    ∀ᶠ t : ℕ in atTop, ∃ r : ℕ,
      Real.exp (rho * (N t : ℝ)) ≤ (r : ℝ) ∧
      TensorObj.Restrict
        (bigAdd (fun _ : Fin r ↦ kronFin 45 (fun c ↦ prescribedZPower
          (cwFourthConstituent K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
          (constituentBasis K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
          (fun a : LiftedCoarseCoordinate.{u} 5 (coarseAddress c 2) ↦
            cwSquarePairGrade 5 a.down.val.1)
          (rawProfile c) (m t c))))
        ((CWObj K 5).kronPow (N t * 4)) := by sorry
