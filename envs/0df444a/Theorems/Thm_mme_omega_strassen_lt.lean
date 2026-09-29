-- Prove2me | Theorems.Thm_mme_omega_strassen_lt
-- name    : mme_omega_strassen_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-28T03:37:47.631424+00:00
-- url     : https://prove2.me/theorems/ea8d45c3-b8fb-4169-9c1e-36980d12b683
-- statement:
--   **Schönhage's bound in Strassen-preorder form:** $\omega_{\mathrm{Strassen}} < 51/20 = 2.55$.
--
--   The matrix-multiplication exponent built from the restriction rank `strassenRank` satisfies $\omega_{\mathrm{Strassen}} < 51/20$. This is the analytic heart of Schönhage's 1981 theorem. It is deliberately stated over the Strassen preorder, because its proof runs through the asymptotic spectrum of tensors, Strassen's duality theorem, the asymptotic sum inequality, and the direct-sum construction $\langle n,1,m\rangle \oplus \langle 1,(n-1)(m-1),1\rangle$ — all theorems about that preorder.
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Definitions.Def_mme_omega_strassen
universe u
open MME

theorem mme_omega_strassen_lt {K : Type u} [Field K] : matMulExp_strassen K < 51 / 20 := by sorry
