-- Prove2me | solution 1 for CRTSplitNoGo.idempotent_reveals
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:57:59.563492+00:00
-- url     : https://prove2.me/submissions/026848a6-46ae-4d1a-97ca-74b5b8849b78

-- Sol generated from Bridges/CRTSplitNoGoBounds.lean
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


/-! ## Regime (a): the verified CTST demo, `N = 341371 = 631 · 541`, `f(x) = x² + 1` -/









open CRTSplitNoGo in
theorem solution{N : ℕ} (hN : 1 < N) (e : ℤ) (hidem : (N : ℤ) ∣ e * (e - 1))
    (h0 : ¬ (N : ℤ) ∣ e) (h1 : ¬ (N : ℤ) ∣ e - 1) : 1 < Int.gcd e (N : ℤ) ∧ Int.gcd e N < N := by
  set g : ℕ := Int.gcd e (N : ℤ) with hg
  have hgN : g ∣ N := Int.ofNat_dvd.mp (by simpa using Int.gcd_dvd_right e (N : ℤ))
  have hgle : g ≤ N := Nat.le_of_dvd (by omega) hgN
  constructor
  · rcases Nat.lt_or_ge 1 g with h | h
    · exact h
    · -- `g ≤ 1`, so `g = 1` and `N` is coprime to `e`, forcing `N ∣ e - 1`
      exfalso
      interval_cases g
      · -- `g = 0` forces `N = 0`
        have : (N : ℤ) = 0 := by
          have := Int.gcd_eq_zero_iff.mp hg.symm
          exact_mod_cast this.2
        simp at this
        omega
      · have hcop : IsCoprime (N : ℤ) e := by
          rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
          exact hg.symm
        exact h1 (hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using hidem))
  · rcases lt_or_eq_of_le hgle with h | h
    · exact h
    · exact absurd (h ▸ (Int.natCast_dvd_natCast.mpr (dvd_refl g)).trans
        (Int.gcd_dvd_left e (N : ℤ))) h0
