-- Prove2me | Definitions.Def_Geometry_Round10Closures_JointClosure
-- name    : Geometry_Round10Closures_JointClosure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:04.625276+00:00
-- url     : https://prove2.me/theorems/1d5a85bd-f93f-4c6a-af7e-4595d6ba2657
-- title:
--   Aether Catalog definitions — Geometry_Round10Closures_JointClosure
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Round10Closures.JointClosure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Round10Closures/JointClosure.lean by skeleton subtraction
import Mathlib
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

namespace Round10

open scoped Classical

/-- The `S`-profile of a modulus `N`: the joint of the free witnesses of all exponents
in the finite set `S` (padded by `0` outside `S`, so that profiles of different moduli
live in one type and can be compared). -/
noncomputable def profile (S : Finset ℕ) (N : ℕ) : ℕ → ℕ :=
  fun k => if k ∈ S then freeWitness N k else 0

/-- Exponent sets used by the round-10 experiments are finite sets of positive integers;
`saturator S` is their product, the modulus of the arithmetic progression along which
every witness in `S` is maximal. -/
def saturator (S : Finset ℕ) : ℕ := ∏ k ∈ S, k










/-! ## Experiment 337 in concrete form

The round-10 experiment used the exponent set `{6, 12, 15, 20, 30, 60}`.  Both `61` and
`181` are primes congruent to `1` modulo `60`, so the semiprimes `61 * 7` and `181 * 7`
have identical joint profiles over that set — a persistent collision one can check by hand.
-/


end Round10


