-- Prove2me | Theorems.Thm_mme_tau_value_le_of_asymptoticRank_le
-- name    : mme_tau_value_le_of_asymptoticRank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-23T23:25:56.597156+00:00
-- url     : https://prove2.me/theorems/93403cbc-a5b3-4d54-a494-61bbc469cd53
-- title:
--   Tau-value is bounded by asymptotic rank
-- statement:
--   Let $T$ be an order-three tensor over a field $K$. Suppose its asymptotic rank is at most a nonnegative real number $R$, and suppose $T$ has unrestricted $\tau$-value at least $V\ge1$ at $\tau=\omega_K/3$. Then $$V\le R.$$ The assertion is the rank upper-bound consequence of the Coppersmith--Winograd value definition and the Schoenhage asymptotic sum inequality. The unrestricted witness retains the exponentially many extracted matrix products; synchronizing its arbitrarily large powers with the asymptotic-rank infimum is part of the theorem.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), value definition and immediate properties, journal p. 264 (PDF p. 14), combined with Schoenhage asymptotic sum inequality; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_tau_value
import Definitions.Def_mme_omega_strassen
open MME
universe u

theorem mme_tau_value_le_of_asymptoticRank_le
    {K : Type u} [Field K] {T : TensorObj K 3} {R V : ℝ}
    (hR_nonneg : 0 ≤ R) (hV_one : 1 ≤ V)
    (hR : tensorAsymptoticRank T ≤ R)
    (hV : HasTauValueAtLeast T (matMulExp_strassen K / 3) V) :
    V ≤ R := by sorry
