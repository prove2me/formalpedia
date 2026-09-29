-- Prove2me | Theorems.Thm_mme_CW_subrank_capacity_poly_lower
-- name    : mme_CW_subrank_capacity_poly_lower
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-05-31T19:31:34.139319+00:00
-- url     : https://prove2.me/theorems/2d35a7cc-4b37-4248-90ee-e8ee0e9edd4a
-- statement:
--   **Laser-method polynomial-witness lower bound on the subrank capacity of $T_6$.**
--
--   For the Coppersmith–Winograd tensor at $q = 6$, the asymptotic laser-method analysis (with polynomial-bounded witness summand counts) yields the polynomial-subrank-capacity bound
--
--   $$\widetilde V_{\mathrm{poly}}\bigl(\mathrm{CWObj}\,K\,6\bigr) \;\geq\; \frac{5}{2}.$$
--
--   Replaces `mme_CW_subrank_capacity_lower` (against the weak `subrankCapacity`) with the correct `subrankCapacityPoly` formulation that pairs with `mme_omega_le_of_subrank_capacity_poly` to discharge L1-α cleanly.
--
--   **Why this works where the old version didn't.** The laser-method construction naturally produces a *polynomial* witness summand count (typically $k_N = O(N^c)$ from the multinomial / Stirling count on Salem–Spencer-indexed blocks). The old `subrankCapacity` didn't enforce this, leaving L1-α's Hölder + asymptotic-limit step too weak to close. This poly version captures the actual laser-method output.
--
--   **Proof status.** Open. Same Layer-2 + Layer-3 structure as `mme_CW_subrank_capacity_lower` (abstract laser theorem applied to CW witness), but threaded through the poly constraint.
-- source:
--   https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_subrank_capacity_poly
open MME
universe u

theorem mme_CW_subrank_capacity_poly_lower {K : Type u} [Field K] : (5 : ℝ) / 2 ≤ subrankCapacityPoly (CWObj K 6) := by sorry
