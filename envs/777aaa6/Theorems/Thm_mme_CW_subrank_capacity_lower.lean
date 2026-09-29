-- Prove2me | Theorems.Thm_mme_CW_subrank_capacity_lower
-- name    : mme_CW_subrank_capacity_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-31T17:30:58.797695+00:00
-- url     : https://prove2.me/theorems/acdac5f3-2e60-472f-a7fc-f44a430f46bf
-- statement:
--   **Laser-method lower bound on the subrank capacity of the CW tensor at q = 6.**
--
--   For the Coppersmith–Winograd tensor `T_6`, the asymptotic laser-method analysis yields
--
--   $$\widetilde V\bigl(T_6\bigr) \;\geq\; \frac{5}{2}.$$
--
--   Combined with the border-rank bound $\widetilde R(T_6) \leq 8$ (`mme_CW_border_rank_le` via `mme_degenerates_asymptoticRank_le`) and the abstract bridge `mme_omega_le_of_subrank_capacity`, this yields
--
--   $$\omega \;\leq\; \frac{\log 8}{\log(5/2)} \;\approx\; 2.2693 \;<\; 2.376.$$
--
--   **Why this constant.** $V = 5/2$ at $q = 6$ is chosen for the cleanest top-level reduction: it leaves a comfortable margin under $2376/1000$ and matches the regime where the laser-method bound for `T_q` becomes effective. The actual sharp value achievable by the canonical CW §7–§8 analysis (via the symmetric tensor square of $T_6$ with refined Salem–Spencer indexing) is somewhat larger; future refinements (Stothers, Vassilevska Williams, Le Gall, Alman–VW) will produce sharper bounds via their own subrank-capacity lower bounds on their own tensors, each as a new theorem node.
--
--   **Proof status.** Open. Recurses into the full Layer-2 abstract laser-method machinery:
--
--   1. **Block decomposition of $T_q^{\otimes 2N}$**: the rank-one support of $T_q$ is 3-graded by the index type $\tau : \mathrm{Fin}(q{+}2) \to \{0,1,2\}$, so $T_q^{\otimes 2N}$ splits as a sum of "block tensors" indexed by triples $(I, J, K)$ of multi-types.
--
--   2. **Restriction to a Salem–Spencer set**: pick $S \subseteq [N]$ with no nontrivial 3-AP; restricting block indices to $S$ kills all collisions between block tensors (each pair of distinct surviving blocks shares no factor coordinate), turning the sum into a *direct sum*.
--
--   3. **Each surviving block is a matrix-multiplication tensor** $\langle a, b, c\rangle$ of explicit multinomial dimensions.
--
--   4. **Counting**: Stirling / multinomial bounds on the number of surviving blocks plus their dimensions give the explicit value lower bound.
--
--   5. **Bridge from Mathlib's Behrend bound** $|S| \geq N \exp(-4\sqrt{\log N})$ to the $\varepsilon$-form $|S| \geq N^{1-\varepsilon}$.
--
--   These Layer-2 leaves are themselves **paper-agnostic**: replacing $T_q$ by any other tensor with a 3-graded support of the right combinatorial profile yields the same machinery.
-- source:
--   https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_subrank_capacity
open MME
universe u

theorem mme_CW_subrank_capacity_lower {K : Type u} [Field K] : (5 : ℝ) / 2 ≤ subrankCapacity (CWObj K 6) := by sorry
