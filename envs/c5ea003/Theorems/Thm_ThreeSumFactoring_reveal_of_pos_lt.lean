-- Prove2me | Theorems.Thm_ThreeSumFactoring_reveal_of_pos_lt
-- name    : ThreeSumFactoring.reveal_of_pos_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:04:44.496977+00:00
-- url     : https://prove2.me/theorems/b38c0b8d-75a5-40cf-85c8-7bfd75e26d9d
-- title:
--   Guaranteed reveal.
-- statement:
--   **Guaranteed reveal.**  Every *positive* multiple of `p` below `N = p*q`
--   reveals `p`; no extra hypothesis mod `q` is needed.  In particular every
--   3SUM-mod-`p` triple with small entries is a factoring witness.
--
--   ```lean
--   theorem ThreeSumFactoring.reveal_of_pos_lt{p q s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
--       (h0 : 0 < s) (hlt : s < p * q) (hps : p ∣ s) : Nat.gcd s (p * q) = p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ThreeSumFactoring.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ThreeSumFactoring.lean#L76

-- Thm stub generated from Applications/ThreeSumFactoring.lean
import Mathlib
import Definitions.Def_Applications_ThreeSumFactoring
/-
# 3SUM mod `p` reveals a factor of `N = p*q`

Let `N = p * q` be a semiprime with `p ≠ q` two primes.  If a triple `(a,b,c)`
satisfies

* `a + b + c ≡ 0 (mod p)`, and
* `a + b + c ≢ 0 (mod q)`,

then `gcd(a+b+c, N) = p`: the triple *reveals* the factor `p`.

The file proves the general gcd lemma behind this observation, the 3SUM
specialisation, and a *guaranteed reveal* theorem which explains the experimental
observation that no small triple is ever divisible by both primes: any positive
sum smaller than `N` that is divisible by `p` is automatically **not** divisible
by `q`, hence always reveals `p`.  A concrete `N = 143 = 11 * 13` census is
verified by kernel computation.

Companion file: `Catalog/Applications/BirthdayBoundHierarchy.lean`, which shows
that the *cost* of finding such a triple obeys the same `√N` barrier as every
other collision-based factoring method.
-/

open ThreeSumFactoring

/-! ## The core arithmetic lemma -/



/-! ## The 3SUM specialisation -/

theorem ThreeSumFactoring.reveal_of_pos_lt{p q s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h0 : 0 < s) (hlt : s < p * q) (hps : p ∣ s) : Nat.gcd s (p * q) = p := by sorry
