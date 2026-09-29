-- Prove2me | Theorems.Thm_KServer_line_competitive
-- name    : KServer.line_competitive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:11:27.801113+00:00
-- url     : https://prove2.me/theorems/7a6b909f-efa8-4cb4-b18b-98a6b7a6b0b4
-- title:
--   The conjecture on the real line (Double Coverage)
-- statement:
--   (Chrobak--Karloff--Payne--Vishwanathan, 1991.) For every $k \ge 1$ and every initial configuration on the real line $\mathbb{R}$ there is a $k$-competitive deterministic online $k$-server algorithm. The witness in the source is the **Double Coverage** algorithm: servers adjacent to the request move toward it at equal speed until one arrives. This matches the lower bound, so the deterministic competitive ratio on the line is exactly $k$.
-- source:
--   Chrobak--Karloff--Payne--Vishwanathan, New results on server problems, SIAM J. Discrete Math. 4 (1991), the theorem that Double Coverage is k-competitive on the real line, https://doi.org/10.1137/0404017

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem line_competitive (k : ℕ) (hk : 1 ≤ k) (C₀ : Config k ℝ) :
    ∃ A : OnlineAlgorithm k ℝ, A.conf [] = C₀ ∧ IsCompetitive A (k : ℝ) := by sorry

end KServer
