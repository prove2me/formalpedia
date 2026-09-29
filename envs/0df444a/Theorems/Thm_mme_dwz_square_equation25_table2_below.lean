-- Prove2me | Theorems.Thm_mme_dwz_square_equation25_table2_below
-- name    : mme_dwz_square_equation25_table2_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T18:19:17.059555+00:00
-- url     : https://prove2.me/theorems/e2369c65-4e33-45cc-98a6-84bb359ab2c5
-- title:
--   DWZ Equation (25), q=6/Table 2: strict-below six-symmetrized restriction witness
-- statement:
--   For every field $K$, every $\tau\ge 2/3$, and every $0\le V<R_{\mathrm{Table\,2}}(\tau)$, where the rate is the closed entropy-and-component expression obtained from Equation (25) using the exact printed Table 2 parameters and the Section 6.3 component lower bounds, the full six-symmetrization of $CW_6^{\otimes 2}$ has an asymptotic direct-sum matrix-multiplication restriction witness of base $V^6$. The strict inequality absorbs the source's subexponential losses. This is a restriction-form, strict-below specialization of Equation (25), rather than the endpoint limsup equation itself; conversion to a direct tau-value witness is a separate CW-square symmetry/root theorem.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023: Definition 3.3 (printed p. 18); Lemmas 4.1 and 4.6 (pp. 30-31); Lemma 6.7 (pp. 54-56); Equation (25), Algorithm 2, Section 6.3, and Table 2 (pp. 58-59).

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_dwz_hole_lemma_cover_core
import Theorems.Thm_mme_dwz_claim6_8_arithmetic
open MME
open MME.DWZSquare
universe u

theorem mme_dwz_square_equation25_table2_below
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V) (hVlt : V < squareRate tau) :
    HasSixSymmetricTauValueAtLeast
      (TensorObj.kron (CWObj K 6) (CWObj K 6)) tau V := by sorry
