-- Prove2me | Theorems.Thm_Round10_freeWitness_odd
-- name    : Round10.freeWitness_odd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:49:40.536111+00:00
-- url     : https://prove2.me/theorems/c207ae1e-1d94-4a85-b303-d2b859a5b0cb
-- title:
--   The trace lemma for an arbitrary odd modulus.
-- statement:
--   **The trace lemma for an arbitrary odd modulus.**
--
--   ```lean
--   theorem Round10.freeWitness_odd{N : ℕ} (hodd : Odd N) (hN : N ≠ 0) (k : ℕ) :
--       freeWitness N k = ∏ p ∈ N.primeFactors, (Nat.totient (p ^ N.factorization p)).gcd k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Round10Closures/CarmichaelThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Round10Closures/CarmichaelThreshold.lean#L55

-- Thm stub generated from Geometry/Round10Closures/CarmichaelThreshold.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_TraceLemma
/-
Round-10 Closures — Part IX (cycle 5): the aggregation depth of an arbitrary odd modulus.

Cycle 4 identified the exact aggregation depth of the free-witness channel for semiprimes
and for squarefree moduli: the least exponent with a maximal witness is `lcm_{r ∣ N}(r-1)`.
Cycle 5 removes the squarefree hypothesis on the odd part: for *every* odd `N`,

    R_k(N) = ∏_{p ∣ N} gcd(φ(p^{v_p(N)}), k),

and the least positive exponent with `R_k(N) = φ(N)` is the Carmichael exponent
`λ(N) = lcm_{p ∣ N} φ(p^{v_p(N)})`.

The only input beyond the previous cycles is the cyclicity of `(ZMod (p^e))ˣ` for odd
primes; the `2`-adic case is genuinely different (the local group is not cyclic for
`8 ∣ N`) and is left open.
-/

open Round10

theorem Round10.freeWitness_odd{N : ℕ} (hodd : Odd N) (hN : N ≠ 0) (k : ℕ) :
    freeWitness N k = ∏ p ∈ N.primeFactors, (Nat.totient (p ^ N.factorization p)).gcd k := by sorry
