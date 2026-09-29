-- Prove2me | Definitions.Def_Combinatorics_Round11CycleIndexFingerprint
-- name    : Combinatorics_Round11CycleIndexFingerprint
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:33:31.13854+00:00
-- url     : https://prove2.me/theorems/08b1da0f-d1e1-4d6a-bc72-36e8ec33dfee
-- title:
--   Aether Catalog definitions — Combinatorics_Round11CycleIndexFingerprint
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.Round11CycleIndexFingerprint`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/Round11CycleIndexFingerprint.lean by skeleton subtraction
import Mathlib
/-
# Round-11 Closures, Part I: the cycle-index fingerprint and its Möbius spectrum

Formal companion to the round-11 negative-results synthesis
(`29_Round11_Closures.md`, hypotheses **CIFINGER** / **CFSIGMA**).

For a semiprime `N = p * q` and a base `b` coprime to `N`, the *cycle-index
fingerprint* is
```
F(c) = gcd (b ^ c - 1) N .
```
The paper asserts three things about it, all of which are proved here in full:

* **Structure.** `F(c) = p^[ord_p b ∣ c] * q^[ord_q b ∣ c]`
  (`Round11.fpr_eq_indicator`).
* **The order seal.** `F(c) = 1` for every `0 < c < min (ord_p b) (ord_q b)`, and
  `F` first becomes informative exactly at `d* = min (ord_p b) (ord_q b)`
  (`Round11.fpr_eq_one_of_lt_dstar`, `Round11.one_lt_fpr_dstar`).
* **The Möbius spectrum.** The Möbius transform of the `p`-adic valuation of the
  fingerprint is the *exact indicator of the multiplicative order*:
  `∑_{c ∣ d} μ(d/c) · v_p(F c) = [ord_p b = d]`
  (`Round11.mobFinger_eq_indicator`).  Consequently the Möbius spectrum is
  supported on the two-element set `{ord_p b, ord_q b}`
  (`Round11.mobFinger_eq_zero_of_lt_dstar`): the Möbius structure is genuine but
  relocates no information below the order scale.

The last consequence is the formal content of the CFSIGMA closure: below the
order scale the fingerprint is a *constant* function of the instance, hence its
fibres cannot separate any secret statistic (see Part III).
-/

namespace Round11

open ArithmeticFunction Finset

/-! ## The fingerprint -/

/-- The cycle-index fingerprint `F(c) = gcd (b^c - 1) N`. -/
def fpr (b N c : ℕ) : ℕ := Nat.gcd (b ^ c - 1) N

/-- The multiplicative order of `b` modulo a prime `p`. -/
noncomputable def ordAt (b p : ℕ) : ℕ := orderOf (b : ZMod p)

/-! ## Basic arithmetic of the fingerprint -/





/-! ## The order seal: no information below `d* = min (ord_p b) (ord_q b)` -/





/-! ## The Möbius spectrum -/


/-- The Möbius transform of the `p`-valuation of the fingerprint (the
"per-coefficient" cycle-index object `M_d` of CIFINGER). -/
def mobFinger (p b N d : ℕ) : ℤ :=
  ∑ c ∈ d.divisors, moebius (d / c) * (((fpr b N c).factorization p : ℕ) : ℤ)




/-- The **`N`-computable** Möbius coefficient of the paper: `M_d` built directly
from the fingerprint *values* (no knowledge of `p` is needed to evaluate it). -/
def mobRaw (b N d : ℕ) : ℤ :=
  ∑ c ∈ d.divisors, moebius (d / c) * ((fpr b N c : ℕ) : ℤ)






end Round11


