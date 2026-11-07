-- Prove2me | Theorems.Thm_ZKSheafPCP_theorem_9_8
-- name    : ZKSheafPCP.theorem_9_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:16:50.026196+00:00
-- url     : https://prove2.me/theorems/b2a0f942-ee24-47a6-a230-2abb265a5a6e
-- title:
--   Theorem 9.8 — from a PZK-PCPP for $C_0\times C_1$ to a PZK-PCP for $\mathrm{RLACSP}$
-- statement:
--   Suppose there is a black-box $\kappa$-local perfect zero-knowledge PCPP for the relation $C_0\times C_1$ with alphabet $\mathbb F(n)$, proof length $\hat l(n)$, query complexity $\hat q(n)$, soundness error $\hat\varepsilon(n)$ and query bound $\hat b(n)$. Then there is a PCP for the relation $(R^{\mathrm{YES}}_{\mathrm{RLACSP}},L^{\mathrm{NO}}_{\mathrm{RLACSP}})[\mathbb F,C_0,C_1,\ell,\tau,q,t]$ with alphabet $\mathbb F(n)$ and
--
--   1. proof length $\hat l(\ell(n))+\ell(n)$;
--   2. query complexity $\hat q(\ell(n))+q(n)+1$;
--   3. soundness error $\max\{\hat\varepsilon(n),\,1-\tau(n)+2\hat\delta(n)(q(n)+1)\}$;
--   4. query bound $\min\bigl(t(n)/(\kappa(\ell(n))\cdot q(n)),\,\hat b(\ell(n))\bigr)$.
--
--   This adapts [BCFGRS17, Theorem 8.9] to simulators with locality greater than one and with a bounded number of queries.
--
--   Differences from the source:
--   - reading: δ̂(n), unbound in the statement → δ̂ is the proximity parameter of the assumed PCPP; reason: Theorem 8.9 of [BCFGRS17] has this form; the PCPP is otherwise given no proximity parameter
--   - reading: "there exists a PCP" → a black-box perfect zero-knowledge PCP; reason: the query bound in the table and the proof sketch mean this
--   - reading: "q(n)" on both sides of the table → the query complexity of the conclusion is qhat(ℓ n) + q n + 1 with q the LACSP locality; reason: the page reuses the letter
--   - reading: t(n)/(κ(ℓ(n))·q(n)), undefined at κ·q = 0 → the natural-number quotient, which is 0 there; reason: for q = 0 and small t the value +∞ would be false: the simulator queries w₀ directly, up to κ per query
--   - reading: a PPT simulator (Definition 3.28) → a simulator in time polynomial in |x|, b̂(ℓ(n)), m; reason: it runs the PCPP simulator, whose time is poly(|x|, q*) with q* = b̂ (Definition 3.27); for polynomial b̂∘ℓ this is PPT
--   - reading: "can be computed in time poly(n)" → a polynomially bounded clock, hypothesis hclock; reason: the relation fixes one clock
--   - reading: "C₀(n), C₁(n)… relative distance τ(n)" → relative distance at least τ, hypothesis hΛ; reason: Definition 9.4
--   - encoding: the parameters as functions of n → PCP parameters indexed by the n of the instance (1ⁿ, g); PCPP parameters l̂, q̂, b̂, κ at ℓ(n), and ε̂, δ̂ at n; reason: the table reads them so; |x| can exceed n
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Theorem 9.8, p.44

import Mathlib
import Definitions.Def_ZKSheafPCP_LacspParams

namespace ZKSheafPCP

open Classical

/-- Theorem 9.8, p.44 (Zeilberger, O'Connor, Gur, Spooner, *Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes*, STOC 2027 submission (manuscript sha256 ac5e528f…)): if there is a black-box `κ`-local perfect zero-knowledge PCPP for `C₀ × C₁` with alphabet `𝔽(n)`, proof length `l̂`, query complexity `q̂`, soundness error
`ε̂(n)` and query bound `b̂`, then there is a PCP for `(R^YES_RLACSP, L^NO_RLACSP)[𝔽, C₀, C₁, ℓ, τ, q, t]` with alphabet `𝔽(n)`, proof length `l̂(ℓ(n)) + ℓ(n)`, query complexity
`q̂(ℓ(n)) + q(n) + 1`, soundness error `max{ε̂(n), 1 - τ(n) + 2δ̂(n)(q(n) + 1)}` and query bound `min(t(n)/(κ(ℓ(n)) · q(n)), b̂(ℓ(n)))`.

**Formalization Note** `δ̂` is unbound on the page; it is the proximity parameter of the PCPP, as in [BCFGRS17, Theorem 8.9]. The conclusion is black-box perfect zero knowledge, as the proof
sketch shows. The PCP's parameters are indexed by the `n` of the instance. The bound `t/(κ · q)` is a natural-number quotient, and `0` when `κ · q = 0`. The simulator runs in time
`poly(|x|, b̂(ℓ(n)), m)`, inherited from Definition 3.27. -/
theorem theorem_9_8 (Λ : LacspParams) (hΛ : Λ.CodesHaveDist) (hclock : PolyBdd Λ.clock)
    (lhat qhat bhat κ : ℕ → ℕ) (εhat δhat : ℕ → ℝ)
    (hPCPP : IsPZKPCPP Λ.ccFamily (fun n => lhat (Λ.ℓ n)) (fun n => qhat (Λ.ℓ n)) εhat δhat
      (fun n => bhat (Λ.ℓ n)) (fun n => κ (Λ.ℓ n))) :
    IsPZKPCPAt lacspIndex Λ.a (fun n => lhat (Λ.ℓ n) + Λ.ℓ n) (fun n => qhat (Λ.ℓ n) + Λ.q n + 1)
      (fun n => max (εhat n) (1 - Λ.τ n + 2 * δhat n * ((Λ.q n : ℝ) + 1)))
      (fun n => min (Λ.t n / (κ (Λ.ℓ n) * Λ.q n)) (bhat (Λ.ℓ n)))
      (fun n => bhat (Λ.ℓ n)) Λ.RYes Λ.LNo := by sorry

end ZKSheafPCP
