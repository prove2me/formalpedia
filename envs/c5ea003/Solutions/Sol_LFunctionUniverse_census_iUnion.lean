-- Prove2me | solution 1 for LFunctionUniverse.census_iUnion
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:43:12.618926+00:00
-- url     : https://prove2.me/submissions/d1b8b2e1-7b4d-4726-bf4d-547e91d71d1b

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

/-- If the absolute value (natAbs) of an integer `x` is at most `m`, then `x` lies in
the symmetric interval `[-m, m]`. -/
theorem mem_Icc_of_natAbs_le {x : ℤ} {m : ℕ} (h : x.natAbs ≤ m) :
    x ∈ Finset.Icc (-(m : ℤ)) m := by
  rw [Finset.mem_Icc, ← abs_le, Int.abs_eq_natAbs]
  exact_mod_cast h









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
theorem solution: ⋃ N, census N = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro d
  rw [Set.mem_iUnion]
  set N := max (max (max d.degree d.conductor) (max d.rootNumberNum.natAbs d.rootNumberDen))
      (max d.eulerCoeffs.length ((d.eulerCoeffs.map Int.natAbs).sum)) with hN
  have hdeg : d.degree ≤ N :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hcon : d.conductor ≤ N :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hrn : d.rootNumberNum.natAbs ≤ N :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hrd : d.rootNumberDen ≤ N :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hlen : d.eulerCoeffs.length ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hsum : (d.eulerCoeffs.map Int.natAbs).sum ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨N, hdeg, hcon, mem_Icc_of_natAbs_le hrn, hrd, hlen, ?_⟩
  intro c hc
  apply mem_Icc_of_natAbs_le
  have hmem : c.natAbs ∈ d.eulerCoeffs.map Int.natAbs := List.mem_map.mpr ⟨c, hc, rfl⟩
  exact le_trans (List.single_le_sum (by intro x _; exact Nat.zero_le x) _ hmem) hsum
