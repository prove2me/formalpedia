-- Prove2me | solution 1 for CRTSplitNoGo.pollard_pm1_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:00:32.719264+00:00
-- url     : https://prove2.me/submissions/5b9a78e1-a6fc-4096-8c65-525173879ae3

-- Sol generated from Bridges/CRTSplitNoGoBounds.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGo
import Definitions.Def_Bridges_CRTSplitNoGoBounds
import Theorems.Thm_CRTSplitNoGo_pollard_pm1_reveal_iff

/-!
# The CRT-Split No-Go, Part II: quantitative barriers and the three regimes

Part I (`CRTSplitNoGo.lean`) showed that for `N = p * q` the factor-revealing event of any
`N`-explicit (i.e. integer-polynomial) iteration is *exactly* an exclusive mod-`p` / mod-`q`
cycle closure.  Here we quantify the cost of such a closure in the three regimes of the
classification, and formalise the circularity barrier.

* **Regime (c), structurally simple maps.**  For the successor map `x ↦ x + 1` the reveal
  time is bounded below by `min p q` (`successor_reveal_lower_bound`), hence by
  `√(N/2)` for balanced semiprimes (`successor_reveal_sqrt_bound`), and — the flagship
  statement — it is **superpolynomial in `log N`**: for every polynomial bound
  `c * (log₂ N)^k` there are semiprimes `N = p q` with `p < q < 2p` on which every reveal
  time exceeds that bound (`successor_reveal_superpolynomial`).

* **Regime (b), smoothness-dependent maps.**  For the Pollard `p-1` style datum `a^M - 1`
  the reveal criterion is exactly an exclusive divisibility of multiplicative orders
  (`pollard_pm1_reveal_iff`), and the exponent `M` must be at least the smaller of the two
  orders (`pollard_pm1_lower_bound`): the cost is governed by the smoothness of
  `ord_p(a)`, a quantity invisible from `N`.

* **Regime (a), generic nonlinear maps.**  Verified on the CTST demo `N = 341371 = 631·541`
  with `f(x) = x² + 1`, seed `2`: the first revealing pair is `(s,t) = (23,36)`, the revealed
  factor is `631`, and this is *exactly* the mod-`631` cycle closure while the mod-`541`
  orbit has not yet closed (`crt_demo_gcd`, `crt_demo_xor`, `crt_demo_closure`).

* **Barrier 6 (circularity).**  Producing a nontrivial CRT idempotent mod `N` *is* factoring
  (`idempotent_reveals`): any map that could separate the CRT components already knows the
  factors.
-/

open CRTSplitNoGo

open Polynomial

/-! ## A gcd is insensitive to the modulus -/



/-! ## Regime (c): the successor map `x ↦ x + 1` -/





/-! ### Exponential beats polynomial -/



/-! ## Regime (b): Pollard `p-1`, smoothness-dependent maps -/



/-! ## Barrier 6: the CRT idempotents are the factors -/


/-! ## Regime (a): the verified CTST demo, `N = 341371 = 631 · 541`, `f(x) = x² + 1` -/









open CRTSplitNoGo in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (a : ℤ) (M : ℕ) (hM : 0 < M) (hrev : RevealsFactor (p * q) (a ^ M - 1)) :
    min (orderOf ((a : ZMod p))) (orderOf ((a : ZMod q))) ≤ M := by
  rcases (pollard_pm1_reveal_iff hp hq hne a M).mp hrev with ⟨h, -⟩ | ⟨h, -⟩
  · exact le_trans (min_le_left _ _) (Nat.le_of_dvd hM h)
  · exact le_trans (min_le_right _ _) (Nat.le_of_dvd hM h)
