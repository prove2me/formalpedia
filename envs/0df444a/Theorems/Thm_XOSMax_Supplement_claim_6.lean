-- Prove2me | Theorems.Thm_XOSMax_Supplement_claim_6
-- name    : XOSMax.Supplement.claim_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:33:46.491798+00:00
-- url     : https://prove2.me/theorems/b7b6675a-a4dd-4757-9719-2e10541892bf
-- title:
--   Claim 6 — Algorithm 1 is a $\max(1,\varepsilon n)$-approximation
-- statement:
--   Let $V$ be a nonempty finite ground set, let $\varepsilon>0$, and let $f$ be an XOS function satisfying $f(\{v\})>0$ for every $v\in V$. Algorithm 1 returns a set $\widetilde X$ satisfying
--   $$
--   f(\widetilde X)\ge \frac{1}{\max\{1,\varepsilon |V|\}}\max_{X\subseteq V}f(X).
--   $$
--   Thus the displayed algorithm supplies the approximation step used in Theorem 1, including the exact small-instance case.
--
--   Differences from the source:
--   - encoding: an $(\varepsilon n)$-maximizer, although the source defines $\alpha$-maximizers only for $\alpha\ge1$ → a $\max(1,\varepsilon n)$-maximizer; reason: when $\varepsilon n<1$, Algorithm 1 enumerates every subset and is exact
--   - encoding: a finite ground set $V$ and the displayed algorithm → a nonempty finite type with a duplicate-free enumeration and the concrete oracle program `alg1`; reason: the representations have the same subsets and the program is exactly Algorithm 1
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Claim 6, pp.3-4

import Mathlib
import Definitions.Def_XOSMax_IsKXOS
import Definitions.Def_XOSMax_IsMaximizerApprox
import Definitions.Def_XOSMax_Supplement_alg1

namespace XOSMax.Supplement

open XOSMax OracleProg

/-- **Claim 6.** A best subset of size at most `⌈1/ε⌉`, as returned by Algorithm 1, is a
`max(1, εn)`-maximizer (Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3,
Claim 6 and its proof, pp.3–4).

**Formalization Note** The paper defines an `α`-maximizer only for `α ≥ 1`. When `εn < 1`,
`⌈1/ε⌉ ≥ n`, so Algorithm 1 checks every subset and is exact; `max 1 (εn)` records that boundary
case. `alg1 ε L` is the literal enumeration and first-best selection in the displayed algorithm. -/
theorem claim_6 {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (ε : ℝ) (hε : 0 < ε)
    (L : List E) (hL : L.Nodup) (hLV : L.toFinset = Finset.univ)
    (f : Finset E → ℝ) (hXOS : ∃ k : ℕ, IsKXOS k f)
    (hpos : ∀ v : E, 0 < f {v}) :
    IsMaximizerApprox Finset.univ (max 1 (ε * Fintype.card E)) f (run f (alg1 ε L)).1 := by sorry

end XOSMax.Supplement
