-- Prove2me | Theorems.Thm_mme_dwz_q6_common_halving_union_matrix_pattern_restriction
-- name    : mme_dwz_q6_common_halving_union_matrix_pattern_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T04:17:04.606361+00:00
-- url     : https://prove2.me/theorems/b890bb39-c78e-4c5e-9c94-74102b576488
-- title:
--   Explicit matrix dimensions from distinct common-halving patterns
-- statement:
--   Let $K$ be a field, $s\in\{13,14\}$, and $N=c_s m$. Suppose a primary hash family of length $2N$ admits a common balanced XY halving. Let $P_X$ be the set of first-half X grade patterns of its entries, and let $P_Y$ be the set of second-half Y grade patterns. Then
--   $$\langle |P_X|6^N,1,|P_Y|6^N\rangle\preceq\operatorname{componentPairRestricted}_K(s,m).$$
--   The extracted block has volume $|P_X||P_Y|6^{2N}$. The formula counts each distinct half-pattern once and includes its independent numeric labels. No injectivity of either half-pattern map is assumed.
-- source:
--   Common-halving matrix extraction, inverse trace word equivalences, and exact numeric word counts for binary pattern unions.

import Theorems.Thm_mme_dwz_q6_common_halving_union_matrix_cardinality_restriction
import Theorems.Thm_mme_coupled_binary_word_union_cardinality
import Definitions.Def_mme_kron_pow_word_reindex
import Mathlib.Logic.Equiv.Fin.Basic

open MME MME.DWZComponentRestriction
universe u
set_option autoImplicit false

theorem mme_dwz_q6_common_halving_union_matrix_pattern_restriction
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    let PX := Finset.univ.image (fun p : Fin A × Fin H ↦
      fun r : Fin N ↦ (family.entry p).val 0 (halving.position (Sum.inl r)))
    let PY := Finset.univ.image (fun p : Fin A × Fin H ↦
      fun r : Fin N ↦ (family.entry p).val 1 (halving.position (Sum.inr r)))
    TensorObj.Restrict (MMObj K (PX.card * 6 ^ N) 1 (PY.card * 6 ^ N))
      (componentPairRestricted K s m) := by sorry
