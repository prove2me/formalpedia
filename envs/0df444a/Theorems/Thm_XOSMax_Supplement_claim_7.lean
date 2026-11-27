-- Prove2me | Theorems.Thm_XOSMax_Supplement_claim_7
-- name    : XOSMax.Supplement.claim_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:34:27.417031+00:00
-- url     : https://prove2.me/theorems/4b7bf38a-a91a-4f27-b57a-ea27903f5df7
-- title:
--   Claim 7 — uniform samples hit a large subset with probability at least $1/2$
-- statement:
--   Put $\rho=\varepsilon n/\log n$ and suppose $\rho\ge2e/(e-2)$. If $|X^*|\ge2$, set $m=\lceil2|X^*|/\rho\rceil$. Among $\lceil n^{1/\varepsilon+1}\rceil$ independent uniform $m$-subsets of $V$, at least one lies in $X^*$ with probability at least $1/2$.
--
--   This is the sampling estimate used in Theorem 2.
--
--   Differences from the source:
--   - encoding: independent uniform random subsets → the uniform finite set of all sample sequences, with twice the number of successful sequences at least the total number; reason: finite counting is exactly the same product probability and avoids division by zero
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Claim 7, p.4

import Mathlib

namespace XOSMax.Supplement

/-- **Claim 7.** Under the paper's lower bound on `ρ = εn / log n`, independent uniform
`m`-subsets, with `m = ⌈2|X*|/ρ⌉`, contain a subset of `X*` with probability at least `1/2`
(Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, Claim 7, p.4).

**Formalization Note** Independent uniform samples are encoded by counting all sequences of
`T = ⌈n^(1/ε+1)⌉` subsets of cardinality `m`. The conclusion `2·good ≥ all` is exactly the
probability lower bound and avoids division by the sample-space cardinality. `Real.log` is the
paper's natural logarithm. -/
theorem claim_7 {E : Type} [Fintype E] [DecidableEq E] (ε ρ : ℝ) (hε : 0 < ε)
    (hρ : ρ = ε * Fintype.card E / Real.log (Fintype.card E))
    (hρmin : 2 * Real.exp 1 / (Real.exp 1 - 2) ≤ ρ)
    (Xstar : Finset E) (hXstar : 2 ≤ Xstar.card) :
    let m := Nat.ceil (2 * (Xstar.card : ℝ) / ρ)
    let T := Nat.ceil (Real.rpow (Fintype.card E) (1 / ε + 1))
    2 * Set.ncard {samples : Fin T → Finset E |
          (∀ j, (samples j).card = m) ∧ ∃ j, samples j ⊆ Xstar} ≥
      Set.ncard {samples : Fin T → Finset E | ∀ j, (samples j).card = m} := by sorry

end XOSMax.Supplement
