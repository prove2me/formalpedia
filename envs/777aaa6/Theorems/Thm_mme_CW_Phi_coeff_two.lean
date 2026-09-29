-- Prove2me | Theorems.Thm_mme_CW_Phi_coeff_two
-- name    : mme_CW_Phi_coeff_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-06-05T01:49:07.030284+00:00
-- url     : https://prove2.me/theorems/2bca352a-c9fc-46a6-bb8d-52892f7cf5e4
-- statement:
--   Order-2 cross-term cancellation for the Coppersmith–Winograd border-rank construction. Given $(q+2:K)\ne 0$ and $\gamma$ with $(q+2)\gamma^2=(1+\gamma)^2$, the CW tensor $T_{q+1}$ degenerates to order $2$ onto the diagonal tensor of size $(q+1)+2$.

import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_degeneration
universe u
open MME

theorem mme_CW_Phi_coeff_two {K : Type u} [Field K]
    (q : ℕ) (γ : K)
    (hQ : (q + 2 : K) ≠ 0)
    (hγ : (q + 2 : K) * γ * γ = (1 + γ) * (1 + γ)) :
    DegeneratesOfOrder (CWObj K (q + 1)) (TensorObj.diagObj K 3 ((q + 1) + 2)) 2 := by sorry
