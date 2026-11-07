-- Prove2me | Theorems.Thm_ZKSheafPCP_theorem_8_18
-- name    : ZKSheafPCP.theorem_8_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:15:53.499194+00:00
-- url     : https://prove2.me/theorems/e57affd5-cfc7-4ad7-bc0b-ed517ed09179
-- title:
--   Theorem 8.18 (corrected: $\epsilon>0$ unless $\delta=1$, $\delta>0$ unless $\epsilon=1$) — a perfect zero-knowledge PCPP for $\mathrm{RS}^+$
-- statement:
--   For all $\epsilon,\delta\in[0,1]$ with $\epsilon>0$ unless $\delta=1$ and $\delta>0$ unless $\epsilon=1$, there is a black-box, $\sqrt n$-local, perfect zero-knowledge PCPP for the Reed–Solomon family $\mathrm{RS}^+$, where $n=|L|$, with
--
--   1. proof length $\tilde O(n)$;
--   2. verifier query complexity $\mathrm{polylog}(n)$;
--   3. zero-knowledge query bound $\sqrt n/8-2$;
--   4. soundness error $\delta$ and proximity parameter $\epsilon$.
--
--   This is the paper's key technical result, the zero-knowledge version of the short PCPP of Ben-Sasson and Sudan.
--
--   **Formalization Note** The explicit input is $(\mathbb F,L,d)$, so the verifier runs in time polylogarithmic in $n$ and in $\log|\mathbb F|$, and the simulator in time polynomial in those and in the query bound.
--
--   Differences from the source:
--   - correction: for all ϵ, δ ∈ [0, 1] → ϵ, δ ∈ [0, 1] with ϵ > 0 unless δ = 1 and δ > 0 unless ϵ = 1; reason: false at δ = 0, ϵ = 1/4 for large |L| (and likewise for every ϵ < 1, using d = 0): fix coins r and an honest (c, π), let y equal c on the polylog(n) positions V reads under r and be free elsewhere; words 1/4-close to RS[F, L, d] with d ≤ |L|/8 number fewer than |F|^{|L|−polylog(n)}, so some such y is 1/4-far and V accepts on r, making the error nonzero. At ϵ = 0 every codeword is 0-far, and completeness contradicts any error below 1. The corners (ϵ, δ) = (1, 0) (no word is 1-far from a code containing the constants) and (0, 1) (error 1 is free) are true and kept
--   - reading: "√n/8 − 2", "√n-local" → ⌊√n/8 − 2⌋ truncated at 0, and ⌈√n⌉; reason: the printed quantities need not be integers when k is odd; both are exact when k is even and n ≥ 256
--   - reading: verifier and simulator time, unstated in Definition 3.25 → verifier time polynomial in |(F, L, d)|; simulator time polynomial in |(F, L, d)|, the query bound and m; reason: Definition 3.27 gives the simulator poly(|x|, q*), and Theorem 9.8 needs an efficient verifier
--   - encoding: Õ(N), polylog(n) → C·n·(log₂(n+2))^c and C·(log₂(n+2))^c, with C, c after ϵ, δ; reason: the proof bounds queries by O(log(1/δ)/(ϵ/polylog n))
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Theorem 8.18, p.41; Construction 8.17, p.41

import Mathlib
import Definitions.Def_ZKSheafPCP_RSIndex

namespace ZKSheafPCP

open Classical

/-- Theorem 8.18, p.41 (Zeilberger, O'Connor, Gur, Spooner, *Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes*, STOC 2027 submission (manuscript sha256 ac5e528f…)), corrected: for all `ϵ, δ ∈ [0, 1]` with `ϵ > 0` unless `δ = 1` and `δ > 0` unless `ϵ = 1`, there exists a black-box, `√n`-local, perfect zero-knowledge PCPP for `RS+`
with proof length `Õ(n)`, verifier query complexity `polylog(n)`, zero-knowledge query bound `√n/8 - 2`, soundness error `δ` and proximity
parameter `ϵ`, where `n = |L|`.

**Formalization Note** The page has `ϵ, δ ∈ [0, 1]`, which is false at `δ = 0` for `ϵ < 1` and at `ϵ = 0` for `δ < 1`. The two corners `(ϵ, δ) = (1, 0)` (no word is `1`-far from a code containing the constants) and `(0, 1)` (error `1` is free) are true and kept. The verifier's clock and the simulator's time are
polynomial in the length of the explicit input `(𝔽, L, d)` and in the query bound. `√n/8 - 2` is floored and truncated at `0`, and `√n` as a
locality is rounded up; both are exact when `k` is even and `n ≥ 256`. -/
theorem theorem_8_18 (ϵ δ : ℝ) (hϵ0 : 0 ≤ ϵ) (hϵ1 : ϵ ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hϵ : 0 < ϵ ∨ δ = 1) (hδ : 0 < δ ∨ ϵ = 1) :
    ∃ (C : ℝ) (c : ℕ) (ℓ q : RSIndex → ℕ),
      (∀ i, (ℓ i : ℝ) ≤ C * i.n * (Real.logb 2 (i.n + 2)) ^ c) ∧
      (∀ i, (q i : ℝ) ≤ C * (Real.logb 2 (i.n + 2)) ^ c) ∧
      IsPZKPCPP rsPlus ℓ q (fun _ => δ) (fun _ => ϵ)
        (fun i => ⌊Real.sqrt i.n / 8 - 2⌋₊) (fun i => ⌈Real.sqrt i.n⌉₊) := by sorry

end ZKSheafPCP
