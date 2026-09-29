-- Prove2me | solution 1 for LFunctionUniverse.census_mono
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:43:13.137162+00:00
-- url     : https://prove2.me/submissions/96a5214c-e8f0-4ce3-8398-a9f2b8a8adcd

-- Sol generated from Applications/LFunctionUniverse/SelbergCensus.lean
import Mathlib
import Definitions.Def_Applications_LFunctionUniverse_SelbergCensus

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

open LFunctionUniverse










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











open LFunctionUniverse in
theorem solution{M N : ℕ} (h : M ≤ N) : census M ⊆ census N := by
  rintro d ⟨h1, h2, h3, h4, h5, h6⟩
  rw [Finset.mem_Icc] at h3
  refine ⟨h1.trans h, h2.trans h, ?_, h4.trans h, h5.trans h, ?_⟩
  · rw [Finset.mem_Icc]
    exact ⟨le_trans (by exact_mod_cast neg_le_neg (by exact_mod_cast h)) h3.1,
      h3.2.trans (by exact_mod_cast h)⟩
  · intro c hc
    have := h6 c hc
    rw [Finset.mem_Icc] at this ⊢
    exact ⟨le_trans (by exact_mod_cast neg_le_neg (by exact_mod_cast h)) this.1,
      this.2.trans (by exact_mod_cast h)⟩
