-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_family_tensor_realization
-- name    : mme_CW_q6_primary_hash_family_tensor_realization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-24T17:55:57.394992+00:00
-- url     : https://prove2.me/theorems/f149688f-2314-4606-a47d-5cee1611fcaf
-- title:
--   Realize an induced q=6 hash family as cyclic C-tensor macro blocks
-- statement:
--   Let \(K\) be any field, and let an induced primary hash family in the \(2N\)-th power of the coupled \(q=6\) constituent have \(A\) outer fibers of common positive size \(H\) and exact profile \((L,L,2G)\). Then the \(2N\)-th power of the cyclic symmetrization has an actual coordinate restriction to
--   \[
--   \bigoplus_{a=1}^{A^3}
--     \left(\langle H,H,H\rangle\otimes S_{L,G}\right),
--   \]
--   where \(S_{L,G}\) is the concrete coupled q=6 survivor tensor.
--
--   The induced condition removes every mixed block outside the selected family. Within each one-orientation fiber, the \(H\) terms share their third-mode block and therefore form \(\langle1,H,1\rangle\), not a direct sum. Multiplying the three cyclic orientations produces the single factor \(\langle H,H,H\rangle\), while independent outer labels give exactly \(A^3\) macro blocks. The statement is purely tensor algebra and uses no counting estimate.
-- source:
--   Tensor realization of the C-tensor construction in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270--271; https://www.sciencedirect.com/science/article/pii/S0747717108800132.

import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_CW_q6_coupled_survivor
open MME BigOperators
universe u

theorem mme_CW_q6_primary_hash_family_tensor_realization
    {K : Type u} [Field K]
    (N L G A H : ℕ) (family : CWQ6PrimaryHashFamily N L G A H) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin (A ^ 3) =>
        TensorObj.kron (MMObj K H H H)
          (coupledQ6Survivor K L G)))
      ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) := by sorry
