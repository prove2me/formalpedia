-- Prove2me | Theorems.Thm_mme_CW_border_rank_le_isSquare
-- name    : mme_CW_border_rank_le_isSquare
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-31T23:13:53.162529+00:00
-- url     : https://prove2.me/theorems/3ac8d0fd-ac08-41b0-b550-3fc665514e40
-- statement:
--   **CW border rank ≤ q+2 under the IsSquare hypothesis.** For any field K and any q ∈ ℕ with `IsSquare ((q+1 : ℕ) : K)`, the Coppersmith-Winograd tensor T_q has border rank ≤ q+2.
--
--   **Why the IsSquare hypothesis.** The standard q+2-slot CW degeneration's order-2 cross-term cancellation forces the equation `q · γ² = (1 + γ)²` for the boundary-slot correction γ, requiring `√(q+1) ∈ K`. Subagent F (2026-05-31) verified this is *necessary* — not just for invertibility of (q+1) but for the off-diagonal cancellation. With s : K, s·s = q+1, the choice γ = (s+1)/q closes the system cleanly.
--
--   **Status.** Open. PARTIAL proof skeleton exists locally (~558 LOC), with the q = 0 case fully PROVED (clean two-slot construction `((-1)·e_O)^⊗3 + (e_O + ε²·e_T)^⊗3`) and the q ≥ 1 case requiring ~500-700 LOC of mechanical coefficient calculus mirroring `Sol_mme_schonhage_degenerates.lean` (600 LOC). The mathematical construction is fully worked out; closing requires single-turn extension of the existing skeleton.
--
--   **Reusability.** The CW-specific instance of border rank ≤ q+2 — used as L1-γ in the v2 reduction of `mme_omega_lt_CW`. Future ω-bound improvements that use CW tensors (Stothers, VW, Le Gall, Alman-VW) all need this fact at q = 6, q = 8 etc. The IsSquare hypothesis suffices when working over the relevant base fields (typically `K = ℂ` where every element is a square).
-- source:
--   https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_degeneration
open MME
universe u

theorem mme_CW_border_rank_le_isSquare {K : Type u} [Field K] (q : ℕ) (hSq : IsSquare ((q + 1 : ℕ) : K)) : Degenerates (CWObj K q) (TensorObj.diagObj K 3 (q + 2)) := by sorry
