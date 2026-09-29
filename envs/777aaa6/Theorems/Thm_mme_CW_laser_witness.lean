-- Prove2me | Theorems.Thm_mme_CW_laser_witness
-- name    : mme_CW_laser_witness
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-05-31T17:44:39.308772+00:00
-- url     : https://prove2.me/theorems/9a099d78-a62e-4f6d-bde1-323ec63706a3
-- statement:
--   **The Coppersmith–Winograd laser-method witness package.**
--
--   For the Coppersmith–Winograd tensor at parameter $q = 6$, this theorem packages the complete laser-method instantiation in a single existential statement: there exist
--
--   - a canonical 3-grading $G$ on the modes of $T_6 = \mathrm{CWObj}\,K\,6$ partitioning each mode's basis $\{0, 1, \ldots, 6, 7\}$ into $\{0\}, \{1, \ldots, 6\}, \{7\}$,
--   - the cyclic-symmetric support pattern $S = \{(0,1,1), (1,0,1), (1,1,0), (0,0,2), (0,2,0), (2,0,0)\} \subseteq (\mathrm{Fin}\,3)^3$,
--   - a proof that $S$ is `LaserSymmetric` and that $T_6$'s rank-one expansion has `LaserAlignedSupport` with respect to $(G, S)$,
--   - and the explicit value-formula lower bound $\tfrac{5}{2} \leq \mathrm{laserValueFormula}\,G\,S$,
--
--   all simultaneously. This is the CW-specific data fed into the abstract laser theorem `mme_laser_value_lower_bound` to derive `mme_CW_subrank_capacity_lower`.
--
--   **Bundling rationale.** The four pieces are bundled into one existential theorem so that the L1-β reduction `sketch_mme_CW_subrank_capacity_lower` does not have to thread multiple separate grading/pattern arguments through the abstract laser theorem; a single `obtain` extracts the witness and an immediate application of the abstract theorem closes the reduction.
--
--   **Status.** Open. Splits in Layer 3 into:
--
--   1. The explicit `CWGrading` construction (with the `DirectSum.IsInternal` proof for the $\{0\}, \{1, \ldots, q\}, \{q+1\}$ partition).
--
--   2. The combinatorial verification that $S$ is closed under cyclic permutation — immediate from the explicit listing.
--
--   3. The structural fact that $T_q$'s $3q + 3$ rank-one terms each have type-triple in $S$ — immediate from the definition of `CWTensor`.
--
--   4. The explicit $\tfrac{5}{2}$ lower bound on `laserValueFormula G S` — the numeric heart, derived from the Salem–Spencer indexing + Stirling counting at the optimal probability distribution on $S$ (the symmetric distribution favouring the type-triple $(1,1,0)$ and its cyclic conjugates).
-- source:
--   https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_tensor_type_grading
import Definitions.Def_mme_laser_pattern
open MME
universe u

theorem mme_CW_laser_witness {K : Type u} [Field K] : ∃ (G : (CWObj K 6).TypeGrading 3) (S : Finset (Fin 3 × Fin 3 × Fin 3)), LaserSymmetric S ∧ TensorObj.LaserAlignedSupport G S ∧ (5 : ℝ) / 2 ≤ laserValueFormula G S := by sorry
