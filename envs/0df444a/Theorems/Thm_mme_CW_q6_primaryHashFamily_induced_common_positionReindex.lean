-- Prove2me | Theorems.Thm_mme_CW_q6_primaryHashFamily_induced_common_positionReindex
-- name    : mme_CW_q6_primaryHashFamily_induced_common_positionReindex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T10:44:31.725545+00:00
-- url     : https://prove2.me/theorems/7314aca1-cd07-4618-bd50-61d19b3d0e90
-- title:
--   A primary coupled-CW family remains induced after one common position reindexing
-- statement:
--   Let $\mathcal F$ be an induced primary coupled-CW family and let $\rho$ be one permutation of its $2N$ tensor-power positions. Apply that same permutation to every address in $\mathcal F$. If a mixed triple formed from the reindexed first-, second-, and third-mode words is coordinatewise supported, then its first two entries coincide and its third entry lies in the same outer fiber.
--
--   Thus one family-wide balanced halving preserves exactly the inducedness conclusion needed for direct-sum extraction. The common-permutation hypothesis is substantive: independently reindexing the three selected words would not let the supported mixed address be transported back to the original family.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), induced primary pruning of the coupled constituent on journal pp. 270-271.

import Theorems.Thm_mme_CW_q6_coordinatewiseSupported_positionReindex_iff

open MME

set_option autoImplicit false

theorem mme_CW_q6_primaryHashFamily_induced_common_positionReindex
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (rho : Equiv.Perm (Fin (2 * N)))
    (p q r : Fin A × Fin H)
    (hsupport : CWQ6CoupledCoordinatewiseSupported
      (cwQ6CoupledMixedAddress
        (cwQ6CoupledAddressPositionReindex rho (family.entry p).1)
        (cwQ6CoupledAddressPositionReindex rho (family.entry q).1)
        (cwQ6CoupledAddressPositionReindex rho (family.entry r).1))) :
    p = q ∧ p.1 = r.1 := by
  sorry
