-- Prove2me | Theorems.Thm_Round10_no_profile_extractor
-- name    : Round10.no_profile_extractor
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:50:10.974174+00:00
-- url     : https://prove2.me/theorems/22c3cbd1-9882-4665-bd73-9fc6138c0fc3
-- title:
--   No aggregation channel.
-- statement:
--   **No aggregation channel.**  There is no function reading only the joint `S`-profile of
--   a semiprime `N = p*q` (with `q` fixed) and returning the other prime factor `p`.
--
--   This is the negative half of barrier 4 in its cleanest form: the aggregation of any finite
--   family of free witnesses is information-theoretically insufficient, so a classical algorithm
--   restricted to that channel cannot factor, whatever its running time.
--
--   ```lean
--   theorem Round10.no_profile_extractor(S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k) {q : ℕ} (hq : q.Prime) :
--       ¬ ∃ F : (ℕ → ℕ) → ℕ, ∀ p : ℕ, p.Prime → q < p → F (profile S (p * q)) = p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Round10Closures/JointClosure.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Round10Closures/JointClosure.lean#L98

-- Thm stub generated from Geometry/Round10Closures/JointClosure.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_JointClosure
import Definitions.Def_Geometry_Round10Closures_TraceLemma
/-
Round-10 Closures — Part II: joint closure of the free-witness classification.

Experiment 337 (JOINTCLOSURE) asked whether *joints* of partial free witnesses
close on the factorisation: given a finite set `S` of exponents, does the vector
`(R_k(N))_{k ∈ S}` determine `p` and `q`?

The answer proved here is a definitive **no**, and the proof is analytic:
Dirichlet's theorem on primes in arithmetic progressions produces infinitely many
primes `p ≡ 1 (mod ∏_{k∈S} k)`, all of which *saturate* every witness in `S`
(`gcd(p-1,k) = k`).  Hence the whole joint profile is constant along an infinite
family of pairwise distinct semiprimes: persistent collisions, no aggregation
channel, and no profile-reading extractor can output a prime factor.
-/

open Round10

open scoped Classical

theorem Round10.no_profile_extractor(S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k) {q : ℕ} (hq : q.Prime) :
    ¬ ∃ F : (ℕ → ℕ) → ℕ, ∀ p : ℕ, p.Prime → q < p → F (profile S (p * q)) = p := by sorry
