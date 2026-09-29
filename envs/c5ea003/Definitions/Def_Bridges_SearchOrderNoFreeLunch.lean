-- Prove2me | Definitions.Def_Bridges_SearchOrderNoFreeLunch
-- name    : Bridges_SearchOrderNoFreeLunch
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T09:50:02.209386+00:00
-- url     : https://prove2.me/theorems/414c028f-8ba7-4b69-bdd4-e25ea3391317
-- title:
--   Aether Catalog definitions — Bridges_SearchOrderNoFreeLunch
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.SearchOrderNoFreeLunch`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/SearchOrderNoFreeLunch.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_MultiTargetTrialDivision
import Definitions.Def_Bridges_TreeSieveLottery

/-!
# No fixed search order escapes the size barrier, and blind moduli are infinite

Two open items from `FUTURE_DIRECTIONS.md` are settled here, both of them
quantitative sharpenings of the round-72 verdicts.

## 1. No-free-lunch for enumeration orders (direction 4)

`MultiTargetTrialDivision.lean` proves that the *ascending* sweep first hits at
`a = min p q`, so its cost is exactly the trial-division cost.  One could hope
that a cleverer, `N`-independent order of candidate values does better.
`enumeration_defeated` shows it cannot: for **every** function `f : ℕ → ℕ` and
every prefix length `K` there are semiprimes — arbitrarily large ones — on which
the first `K` probes of `f` all miss.  The reason is structural and matches the
lottery analysis: an `N`-independent prefix is a finite set of integers, and a
finite set of integers only ever exposes the primes below its maximum.

## 2. The blind moduli form an infinite family, for every norm form (direction 3)

`NormFormBlindness.lean` shows that a search whose values are primitively
represented by `x² + D y²` has `gcd(value, N) = 1` whenever every prime factor
of `N` is inert.  Here we show that this is not a measure-zero curiosity:
by Dirichlet's theorem on primes in arithmetic progressions the set of blind
composite moduli is *infinite*, both for `D = 1` (factors `≡ 3 mod 4`,
`infinite_blindOne_semiprimes`) and for `D = 2` (factors `≡ 5 mod 8`,
`infinite_blindTwo_semiprimes`).

## 3. Capstone

`enumeration_and_hypotenuse_face_both_defeated` combines the two: given any
enumeration order and any prefix length, there is a semiprime, larger than any
prescribed bound, on which the order's whole prefix misses *and* on which the
entire (infinite) Berggren hypotenuse face has gcd `1`.  The two failure modes
are simultaneous, so trading one for the other cannot help.
-/

namespace SearchOrder

open MultiTarget TreeSieve

/-! ## Part 1 — no `N`-independent enumeration order beats the size barrier -/



/-! ## Part 2 — the blind moduli are infinite -/

/-- `N` is *blind* for the form `x² + y²`: no primitively represented value of
the form shares a factor with `N`. -/
def BlindOne (N : ℕ) : Prop :=
  ∀ a b c : ℤ, (∀ r : ℕ, r.Prime → ¬ ((r : ℤ) ∣ a ∧ (r : ℤ) ∣ b)) →
    a ^ 2 + b ^ 2 = c → Int.gcd c (N : ℤ) = 1

/-- `N` is *blind* for the form `x² + 2y²`. -/
def BlindTwo (N : ℕ) : Prop :=
  ∀ a b c : ℤ, (∀ r : ℕ, r.Prime → ¬ ((r : ℤ) ∣ a ∧ (r : ℤ) ∣ b)) →
    a ^ 2 + 2 * b ^ 2 = c → Int.gcd c (N : ℤ) = 1










/-! ## Part 3 — both failure modes strike at once -/


end SearchOrder


