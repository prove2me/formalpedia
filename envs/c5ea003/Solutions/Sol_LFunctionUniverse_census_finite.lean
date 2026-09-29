-- Prove2me | solution 1 for LFunctionUniverse.census_finite
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:43:12.050815+00:00
-- url     : https://prove2.me/submissions/9f335917-f654-4c12-b7ef-324a9c70391f

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
theorem solution(N : ℕ) : (census N).Finite := by
  -- lists of bounded length over the finite alphabet `[-N, N]` are finite
  have hlists : {l : List ℤ | l.length ≤ N ∧ ∀ c ∈ l, c ∈ Finset.Icc (-(N : ℤ)) N}.Finite := by
    have hfin := List.finite_length_le ↥(Finset.Icc (-(N : ℤ)) N) N
    apply (hfin.image (fun l => l.map Subtype.val)).subset
    rintro l ⟨hlen, hmem⟩
    refine ⟨l.attachWith _ (fun c hc => hmem c hc), ?_, ?_⟩
    · simp [List.length_attachWith, hlen]
    · simp [List.attachWith, List.map_pmap]
  -- the whole slice injects into a finite product
  have hsub : census N ⊆
      (fun p : ℕ × ℕ × ℤ × ℕ × List ℤ =>
          (⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩ : SelbergDatum)) ''
        (Set.Iic N ×ˢ Set.Iic N ×ˢ (Finset.Icc (-(N : ℤ)) N : Set ℤ) ×ˢ Set.Iic N ×ˢ
          {l : List ℤ | l.length ≤ N ∧ ∀ c ∈ l, c ∈ Finset.Icc (-(N : ℤ)) N}) := by
    rintro ⟨deg, con, rn, rd, ec⟩ ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨(deg, con, rn, rd, ec), ⟨h1, h2, h3, h4, h5, h6⟩, rfl⟩
  apply Set.Finite.subset _ hsub
  apply Set.Finite.image
  apply Set.Finite.prod (Set.finite_Iic N)
  apply Set.Finite.prod (Set.finite_Iic N)
  apply Set.Finite.prod (Finset.Icc (-(N : ℤ)) N).finite_toSet
  exact Set.Finite.prod (Set.finite_Iic N) hlists
