-- Prove2me | Theorems.Thm_CRTSplitNoGo_crt_demo_first_reveal
-- name    : CRTSplitNoGo.crt_demo_first_reveal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:37:19.457094+00:00
-- url     : https://prove2.me/theorems/45144293-1dbb-46f7-a8f6-12bb041fcb0c
-- title:
--   Minimality of the CTST reveal.
-- statement:
--   **Minimality of the CTST reveal.**  No pair of times `s < t ≤ 35` reveals a factor of
--   `341371 = 631 · 541` along the orbit of `x ↦ x² + 1` from the seed `2`.  Together with
--   `crt_demo_gcd` (a reveal at `(23,36)`) this identifies `t = 36` as the exact first reveal
--   time, i.e. as the first mod-`631` cycle closure.
--
--   ```lean
--   theorem CRTSplitNoGo.crt_demo_first_reveal(s t : ℕ) (hst : s < t) (ht : t ≤ 35) :
--       ¬ RevealsFactor (631 * 541) (polyOrbit (X ^ 2 + 1) 2 t - polyOrbit (X ^ 2 + 1) 2 s) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CRTSplitNoGoMinimality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CRTSplitNoGoMinimality.lean#L87

-- Thm stub generated from Bridges/CRTSplitNoGoMinimality.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGo
import Definitions.Def_Bridges_CRTSplitNoGoBounds

/-!
# The CRT-Split No-Go, Part III: minimality of the reveal time and the multiplicative regime

Two deepenings of Parts I–II.

* **Minimality of the CTST reveal (regime (a), fully verified).**  For the demo
  `N = 341371 = 631·541`, `f(x) = x²+1`, seed `2`, *no* pair `s < t ≤ 35` reveals a factor
  (`crt_demo_first_reveal`).  Combined with `crt_demo_gcd` this pins the first reveal at
  `t = 36`, which is exactly the first mod-`631` cycle closure — and `√631 ≈ 25.1`, so the
  reveal time sits at the birthday scale `√p`, not at any polynomial in `log N ≈ 18.4`.

  The proof is *not* a brute-force gcd check: it goes through the structural theorem
  `no_reveal_before_closure`, so what is verified computationally is only the injectivity of
  the two reduced orbits — precisely the mechanism the theory predicts.

* **The multiplicative regime (bridge between regimes (b) and (c)).**  For `x ↦ a·x` the
  reveal time is bounded below by the smaller multiplicative order of `a`
  (`multiplicative_reveal_lower_bound`), the exact group-theoretic analogue of the
  arithmetic bound `min p q` for `x ↦ x+1`.

## Lab Notes (experiment CTST, replicated)

Pollard-rho map `x ↦ x²+1`, seed `2`, first revealing pair `(s,t)` for random balanced
semiprimes `N = p·q`; `r = t / √(min p q)`:

```
bits  p       q       (s,t)      factor   r      log₂ t
 9    509     257     (0,9)      509      0.56   3.17
10    1013    827     (14,31)    1013     1.08   4.95
11    1951    1627    (33,40)    1627     0.99   5.32
12    3923    3259    (37,63)    3923     1.10   5.98
13    7789    6073    (21,81)    6073     1.04   6.34
14    12437   15373   (84,113)   12437    1.01   6.82
15    30367   24517   (15,146)   30367    0.93   7.19
16    58943   62219   (173,218)  58943    0.90   7.77
17    97547   115067  (303,422)  97547    1.35   8.72
18    147011  177623  (223,364)  147011   0.95   8.51
19    325081  347587  (423,523)  325081   0.92   9.03
```

`r` stays `O(1)` (mean 0.66–1.59 over the whole range) while `log₂ t` grows linearly in the
bit size: the reveal time tracks `√p = N^{1/4}`, i.e. it is exponential in `log N`.  In every
run the revealed factor is exactly the prime whose reduced orbit closed first.
-/

open CRTSplitNoGo

open Polynomial

/-! ## The mod-`N` trace computes the reduced orbit -/




/-! ## Verified injectivity of the two reduced orbits up to time 35 -/

theorem CRTSplitNoGo.crt_demo_first_reveal(s t : ℕ) (hst : s < t) (ht : t ≤ 35) :
    ¬ RevealsFactor (631 * 541) (polyOrbit (X ^ 2 + 1) 2 t - polyOrbit (X ^ 2 + 1) 2 s) := by sorry
