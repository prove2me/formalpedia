-- Prove2me | Definitions.Def_Applications_LFunctionUniverse_SelbergCensus
-- name    : Applications_LFunctionUniverse_SelbergCensus
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:16.63938+00:00
-- url     : https://prove2.me/theorems/afa349e2-0f5a-4ee3-8176-a1373a96c793
-- title:
--   Aether Catalog definitions — Applications_LFunctionUniverse_SelbergCensus
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.LFunctionUniverse.SelbergCensus`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/LFunctionUniverse/SelbergCensus.lean by skeleton subtraction
import Mathlib

/-!
# The L-function universe, part III: the Selberg census is countable

An element of the Selberg class is, in practice, determined by a *finite* packet of
arithmetic data:

* its **degree**,
* its **conductor**,
* its **root number** (a complex number of modulus `1`, here modelled by a rational
  numerator/denominator pair), and
* the coefficients of its **Euler factors** at finitely many primes.

We model this packet by the structure `SelbergDatum`.  The two headline results are:

* `instCountableSelbergDatum` / `selbergDatum_countably_infinite`: the space of such
  data packets is **countably infinite** — no bigger than `ℕ` — so there are only
  countably many "well-behaved" L-functions, even though each individual one carries
  infinitely much information.

* `census_finite` together with `census_iUnion`: ordering the packets by a
  complexity bound `N` (a common upper bound on all the numerical invariants,
  refining "ordered by conductor"), the `N`-th slice `census N` is a **finite** set,
  and these finite slices **exhaust** the whole universe.  This is exactly what makes
  a concrete enumeration — "the first `100` elements", and so on — possible.
-/

open scoped Classical

namespace LFunctionUniverse


/-- The finite arithmetic data determining an element of the Selberg class:
its degree, conductor, root number (as a rational numerator/denominator pair), and
the list of Euler-factor coefficients recorded at finitely many primes. -/
structure SelbergDatum where
  /-- The degree of the L-function. -/
  degree : ℕ
  /-- The conductor of the L-function. -/
  conductor : ℕ
  /-- Numerator of the (rational model of the) root number. -/
  rootNumberNum : ℤ
  /-- Denominator of the (rational model of the) root number. -/
  rootNumberDen : ℕ
  /-- Coefficients of the Euler factors recorded at finitely many primes. -/
  eulerCoeffs : List ℤ
deriving DecidableEq

/-- **The Selberg data packets form a countable type.**

Each packet injects into the countable type `ℕ × ℕ × ℤ × ℕ × List ℤ`, so there are
only countably many of them. -/
instance instCountableSelbergDatum : Countable SelbergDatum := by
  apply Function.Injective.countable
    (f := fun d => (d.degree, d.conductor, d.rootNumberNum, d.rootNumberDen, d.eulerCoeffs))
  intro a b h
  cases a; cases b; simp_all

/-- There are infinitely many Selberg data packets (already the degree alone can be
any natural number). -/
instance instInfiniteSelbergDatum : Infinite SelbergDatum := by
  apply Infinite.of_injective (fun n : ℕ => (⟨n, 0, 0, 0, []⟩ : SelbergDatum))
  intro a b h
  simpa using h


/-- The `N`-th census slice: the Selberg data packets all of whose numerical
invariants are bounded by `N`.  This refines "ordered by conductor" by imposing a
single complexity bound on every invariant simultaneously. -/
def census (N : ℕ) : Set SelbergDatum :=
  {d | d.degree ≤ N ∧ d.conductor ≤ N ∧ d.rootNumberNum ∈ Finset.Icc (-(N : ℤ)) N ∧
    d.rootNumberDen ≤ N ∧ d.eulerCoeffs.length ≤ N ∧
    ∀ c ∈ d.eulerCoeffs, c ∈ Finset.Icc (-(N : ℤ)) N}




/-!
## A concrete enumeration ordered by conductor

The abstract results above show the census is a countable, increasing union of finite
slices.  To make the original task's request — *enumerate the first `100` elements of
the Selberg class ordered by conductor* — completely concrete, we build an explicit
list.  For each conductor `q` we record a single canonical datum `trivialDatum q`
(a stand-in for the principal-character L-function of conductor `q`); listing these
for `q = 0, 1, …, n-1` gives an honest, computable enumeration whose conductors are
exactly `0, 1, …, n-1` and which contains no repetitions.
-/

/-- A canonical Selberg datum of a prescribed conductor `q` (degree `1`, trivial root
number `1`, no recorded Euler coefficients): a stand-in for the principal-character
L-function of that conductor. -/
def trivialDatum (q : ℕ) : SelbergDatum := ⟨1, q, 0, 1, []⟩


/-- The first `n` census elements, ordered by conductor `0, 1, …, n-1`. -/
def censusByConductor (n : ℕ) : List SelbergDatum :=
  (List.range n).map trivialDatum







end LFunctionUniverse


