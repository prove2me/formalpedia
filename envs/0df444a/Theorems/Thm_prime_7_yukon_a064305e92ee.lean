-- Prove2me | Theorems.Thm_prime_7_yukon_a064305e92ee
-- name    : prime_7_yukon_a064305e92ee
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T04:17:53.808231+00:00
-- url     : https://prove2.me/theorems/21451ee4-b97a-44a8-80b8-7797123d41ed
-- title:
--   prime_7
-- statement:
--   Source declaration prime_7.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/PrattCertificate.lean
--
--   yukon-proof-operation:a73496fa-eca1-4589-ab88-10ed181a8937; Yukon contributor: historical-source-bootstrap
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YTczNDk2ZmEtZWNhMS00NTg5LWFiODgtMTBlZDE4MWE4OTM3OyBZdWtvbiBjb250cmlidXRvcjogaGlzdG9yaWNhbC1zb3VyY2UtYm9vdHN0cmFwIiwiaGFzaCI6IjgxMzQ1N2JhNTY4MWJhNjc4MmRiMWJiNDQwMjhiM2QwYjRjZTY4MTdjZmQyZTQyZTkzMjBkYzQzOWVmODNiZDIiLCJraW5kIjoicHJvYmxlbSIsInRhcmdldCI6InByaW1lXzdfeXVrb25fYTA2NDMwNWU5MmVlIiwiZW52aXJvbm1lbnQiOnsidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIiwibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQifSwidGFnIjoiYmV0dGVyLWNvZGVzLWhpc3RvcnkifQ]

/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.NumberTheory.LucasPrimality


@[expose] public section
/-!
# The Lucas test for primes.

This file implements the Lucas test for primes (not to be confused with the Lucas-Lehmer test for
Mersenne primes). A number `a` witnesses that `n` is prime if `a` has order `n-1` in the
multiplicative group of integers mod `n`. This is checked by verifying that `a^(n-1) = 1 (mod n)`
and `a^d ≠ 1 (mod n)` for any divisor `d | n - 1`. This test is the basis of the Pratt primality
certificate.

## TODO

- Bonus: Show the reverse implication i.e. if a number is prime then it has a Lucas witness.
  Use `Units.IsCyclic` from `RingTheory/IntegralDomain` to show the group is cyclic.
- Write a tactic that uses this theorem to generate Pratt primality certificates
- Integrate Pratt primality certificates into the norm_num primality verifier

## Implementation notes

Note that the proof for `lucas_primality` relies on analyzing the multiplicative group
modulo `p`. Despite this, the theorem still holds vacuously for `p = 0` and `p = 1`: In these
cases, we can take `q` to be any prime and see that `hd` does not hold, since `a^((p-1)/q)` reduces
to `1`.
-/

@[expose] public section

section New

-- TODO: port to `Mathlib`?
end New
-- cannot do ^1 correctly it seems?

theorem prime_7_yukon_a064305e92ee : Nat.Prime 7  := by sorry
end
end
