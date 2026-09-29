-- Prove2me | Theorems.Thm_CRTSplitNoGo_idempotent_reveals
-- name    : CRTSplitNoGo.idempotent_reveals
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:37:33.745957+00:00
-- url     : https://prove2.me/theorems/6506efd1-9293-494e-9592-55c67c56d293
-- title:
--   Circularity.
-- statement:
--   **Circularity.**  A nontrivial idempotent mod `N` (equivalently, a CRT splitting of
--   `ZMod N`) immediately yields a nontrivial factor of `N`.  Hence any procedure that separates
--   the two CRT components must already know the factorisation.
--
--   ```lean
--   theorem CRTSplitNoGo.idempotent_reveals{N : ℕ} (hN : 1 < N) (e : ℤ) (hidem : (N : ℤ) ∣ e * (e - 1))
--       (h0 : ¬ (N : ℤ) ∣ e) (h1 : ¬ (N : ℤ) ∣ e - 1) : 1 < Int.gcd e (N : ℤ) ∧ Int.gcd e N < N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CRTSplitNoGoBounds.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CRTSplitNoGoBounds.lean#L207

-- Thm stub generated from Bridges/CRTSplitNoGoBounds.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGo
import Definitions.Def_Bridges_CRTSplitNoGoBounds

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

theorem CRTSplitNoGo.idempotent_reveals{N : ℕ} (hN : 1 < N) (e : ℤ) (hidem : (N : ℤ) ∣ e * (e - 1))
    (h0 : ¬ (N : ℤ) ∣ e) (h1 : ¬ (N : ℤ) ∣ e - 1) : 1 < Int.gcd e (N : ℤ) ∧ Int.gcd e N < N := by sorry
