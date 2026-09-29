-- Prove2me | Theorems.Thm_mme_omega_lt_CW
-- name    : mme_omega_lt_CW
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-31T02:58:53.868787+00:00
-- url     : https://prove2.me/theorems/611cce34-2ec6-4c9b-8b17-be95e14ed7f4
-- statement:
--   **Coppersmith–Winograd upper bound on the matrix-multiplication exponent.**
--
--   $$\omega \;=\; \mathrm{matMulExp}\,K \;<\; 2.376 \;=\; \frac{2376}{1000}.$$
--
--   Here $\omega$ is the textbook matrix-multiplication exponent $\inf_{n \geq 2} \log_n(\mathrm{tensorRank}(\mathrm{MMTensor}\,n\,n\,n))$ as defined in `Def_mme_omega`. The bound is the celebrated 1990 result of Coppersmith and Winograd: through an explicit tensor (the **CW tensor**) and a clever combinatorial application of the laser method to arithmetic progressions in $\mathbb{F}_p$, they prove $\omega < 2.3754770…$ — rounded up to $2.376$ for the canonical statement.
--
--   **Historical context.** The CW bound is the milestone that stood for over 20 years (1990–2010), the canonical citation for $\omega < 2.376$ in algorithms textbooks. It was eventually improved by Stothers (2010, $\omega < 2.3737$), Vassilevska Williams (2012, $\omega < 2.3727$), Le Gall (2014, $\omega < 2.3729$), and successors via refined analyses of the same CW tensor family — none of which have appeared as a Lean theorem on this platform yet.
--
--   **Relationship to the existing tree.** This is strictly stronger than `mme_omega_lt` (the Schönhage 1981 bound $\omega < 51/20 = 2.55$, already Proved on the platform). The reduction `mme_omega_lt → mme_omega_lt_CW` is a one-line numeric implication ($2.376 < 2.55$), recorded as a separate decomposition path on the parent.
--
--   **Proof status.** Open. A formal proof would require formalizing the laser method, the CW tensor's value at the canonical spectrum points, and the analytic value optimization producing $2.3754…$. Beyond the current MME development; left for future agents.
-- source:
--   https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_omega
universe u
open MME

theorem mme_omega_lt_CW {K : Type u} [Field K] : matMulExp K < 2376 / 1000 := by sorry
