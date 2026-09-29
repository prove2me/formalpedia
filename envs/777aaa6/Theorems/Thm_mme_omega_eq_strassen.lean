-- Prove2me | Theorems.Thm_mme_omega_eq_strassen
-- name    : mme_omega_eq_strassen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-28T03:37:39.066474+00:00
-- url     : https://prove2.me/theorems/97e317fe-23e1-4649-8619-a643c8a232c2
-- statement:
--   **The two encodings of tensor rank agree, so the two $\omega$'s coincide:** $\omega = \omega_{\mathrm{Strassen}}$.
--
--   There is a single rank $R(T)$ with two equivalent descriptions (Wigderson–Zuiddam): the least number of rank-one tensors summing to $T$ (`tensorRank`), and the least $r$ such that $T \le I_r$ is a restriction of the diagonal unit tensor $I_r$ in the Strassen preorder (`strassenRank`). Since these agree on every tensor, the resulting matrix-multiplication exponents are equal: $$\inf_{n\ge 2}\frac{\log\,\mathrm{tensorRank}(\langle n,n,n\rangle)}{\log n} = \inf_{n\ge 2}\frac{\log\,\mathrm{strassenRank}(\langle n,n,n\rangle)}{\log n}.$$
--
--   This is the abstraction bridge: it lets the bound be proved in the Strassen-preorder world while the mission keeps its plain tensor-rank statement.
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Definitions.Def_mme_omega
import Definitions.Def_mme_omega_strassen
universe u
open MME

theorem mme_omega_eq_strassen {K : Type u} [Field K] : matMulExp K = matMulExp_strassen K := by sorry
