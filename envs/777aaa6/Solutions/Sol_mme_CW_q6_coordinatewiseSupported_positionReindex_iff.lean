-- Prove2me | solution 1 for mme_CW_q6_coordinatewiseSupported_positionReindex_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T10:43:10.615796+00:00
-- url     : https://prove2.me/submissions/19d1a6a5-f432-4fd5-9676-cc407a51e061

import Definitions.Def_mme_CW_q6_common_paired_halving

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {N : ℕ} (rho : Equiv.Perm (Fin (2 * N)))
    (address : CWQ6CoupledAddress N) :
    CWQ6CoupledCoordinatewiseSupported
        (cwQ6CoupledAddressPositionReindex rho address) ↔
      CWQ6CoupledCoordinatewiseSupported address := by
  constructor
  · intro h j
    simpa [cwQ6CoupledAddressPositionReindex] using h (rho.symm j)
  · intro h j
    exact h (rho j)
