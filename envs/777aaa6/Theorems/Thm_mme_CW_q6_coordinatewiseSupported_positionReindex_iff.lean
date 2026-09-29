-- Prove2me | Theorems.Thm_mme_CW_q6_coordinatewiseSupported_positionReindex_iff
-- name    : mme_CW_q6_coordinatewiseSupported_positionReindex_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T10:41:21.773946+00:00
-- url     : https://prove2.me/theorems/e353d43f-d7bc-4ddc-a849-bb328a49bdf5
-- title:
--   Coupled-CW coordinatewise support is invariant under common position reindexing
-- statement:
--   For a coupled Coppersmith--Winograd address on $2N$ positions, simultaneously permuting every mode word by the same position permutation preserves coordinatewise support in both directions. Equivalently, the property that every coordinate has one of the four supported types $000,111,012,102$ is independent of the enumeration of tensor-power positions.
--
--   This is the exact invariance needed when one common balanced halving is used to route an entire primary hash family through two paired source powers.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), the four supported coupled-constituent types on journal pp. 266 and 270.

import Definitions.Def_mme_CW_q6_common_paired_halving

open MME

set_option autoImplicit false

theorem mme_CW_q6_coordinatewiseSupported_positionReindex_iff
    {N : ℕ} (rho : Equiv.Perm (Fin (2 * N)))
    (address : CWQ6CoupledAddress N) :
    CWQ6CoupledCoordinatewiseSupported
        (cwQ6CoupledAddressPositionReindex rho address) ↔
      CWQ6CoupledCoordinatewiseSupported address := by
  sorry
