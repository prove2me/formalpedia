-- Prove2me | Theorems.Thm_mme_CW_canonical_aligned_witness
-- name    : mme_CW_canonical_aligned_witness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-31T19:18:13.720166+00:00
-- url     : https://prove2.me/theorems/4e15abac-3139-4bfe-b7ba-4272163a113a
-- statement:
--   **The CW tensor admits the canonical 3-grading with laser-aligned support.**
--
--   For every parameter $q$, there exists a 3-grading $G$ on $\mathrm{CWObj}\,K\,q$ (partitioning each mode's basis as $\{0\} \sqcup \{1, \ldots, q\} \sqcup \{q+1\}$) such that the CW tensor's rank-one expansion has `LaserAlignedSupport` with respect to $G$ and the canonical CW support pattern:
--
--   $$\exists\; G : (\mathrm{CWObj}\,K\,q)\text{.TypeGrading}\;3,\quad \mathrm{TensorObj.LaserAlignedSupport}\;G\;\mathrm{CWSupportPattern}.$$
--
--   **Sub-claims (Layer-4):**
--
--   1. **Existence of the canonical 3-grading.** Each mode $\mathrm{Fin}\,(q+2) \to K$ decomposes as the direct sum $\mathrm{span}\{e_0\} \oplus \mathrm{span}\{e_1, \ldots, e_q\} \oplus \mathrm{span}\{e_{q+1}\}$. The `DirectSum.IsInternal` proof is a standard basis-partition argument, $\sim$80 LOC using `Submodule.iSupIndep` from Mathlib's direct-sum API.
--
--   2. **Type-alignment of CW's rank-one expansion.** The $3q + 3$ rank-one terms of `CWTensor K q` each have factor-indices with type-triple in `CWSupportPattern`:
--      * The "middle" terms $e_0 \otimes e_i \otimes e_i$, $e_i \otimes e_0 \otimes e_i$, $e_i \otimes e_i \otimes e_0$ for $i = 1, \ldots, q$ have type-triples $(0,1,1), (1,0,1), (1,1,0)$ ✓
--      * The "boundary" terms $e_0 \otimes e_0 \otimes e_{q+1}$, $e_0 \otimes e_{q+1} \otimes e_0$, $e_{q+1} \otimes e_0 \otimes e_0$ have type-triples $(0,0,2), (0,2,0), (2,0,0)$ ✓
--
--      A direct case-analysis on `CWTensor` definition.
--
--   **Reusability.** CW-specific structural claim, but the abstract pattern — "given a tensor with explicit basis and a type-partition, the type-aligned support hypothesis can be verified by case analysis" — is reusable for Stothers, VW, Le Gall analogues.
-- source:
--   https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_CW_support_pattern
import Definitions.Def_mme_tensor_type_grading
import Definitions.Def_mme_laser_pattern
open MME
universe u

theorem mme_CW_canonical_aligned_witness {K : Type u} [Field K] (q : ℕ) : ∃ G : (CWObj K q).TypeGrading 3, TensorObj.LaserAlignedSupport G CWSupportPattern := by sorry
