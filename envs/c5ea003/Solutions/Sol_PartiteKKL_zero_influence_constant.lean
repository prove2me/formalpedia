-- Prove2me | solution 1 for PartiteKKL.zero_influence_constant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:16:19.760136+00:00
-- url     : https://prove2.me/submissions/f5392bfc-0bd9-4fc0-be0e-7acfb64217c6

-- Sol generated from Novelty/LocalToGlobalKKLConnector.lean
import Mathlib
import Definitions.Def_Novelty_LocalToGlobalKKLConnector
import Theorems.Thm_PartiteKKL_eq_of_inf_zero

/-!
# A Local-to-Global KKL Theorem for Partite Simplicial Complexes over an Arbitrary Alphabet

This file develops a *local-to-global* principle for coordinate influences on the
complete `n`-partite simplicial complex whose colour classes each have `m`
vertices, in the spirit of the Kahn–Kalai–Linial (KKL) influence theorem and the
high-dimensional-expander "local-to-global" machinery (Kahn–Kalai–Linial 1988;
Bafna–Hoory–Kaufman 2022; Gur–Lifshitz–Liu 2022; Gotlib–Kaufman 2023).

## The complex and its links

The facets (top-dimensional simplices) of the complete `n`-partite complex with
parts of size `m` are exactly the *transversals*: functions `x : Fin n → Fin m`
choosing one vertex from each colour class.  A Boolean labelling of the facets is a
function `f : (Fin n → Fin m) → Bool`.

For a colour `i`, two facets are **`i`-adjacent** when they agree on every colour
`k ≠ i` and differ at colour `i`.  The (unnormalised) **influence** `Inf f i`
counts the ordered `i`-adjacent facet pairs on which `f` changes value — the edges
of the `i`-th Hamming direction that are sensitive for `f`.

Pinning colour `j` to a vertex `b` cuts out the **link** of that vertex: the
subcomplex of facets `x` with `x j = b`.  `InfSub f j b i` counts the sensitive
`i`-edges lying inside that link.

The Boolean cube studied classically is the special case `m = 2`; here every
vertex has `m` links rather than two.

## Results

* `inf_decomp` — the **self-averaging bridge**: every global influence splits as
  the sum of the influences over the `m` links of any fixed colour,
  `Inf f i = ∑ b, InfSub f j b i`.
* `linktot_decomp` — summing the bridge over colours gives the local-to-global
  decomposition of the total influence.
* `localToGlobal_KKL_partite` — the flagship statement: if all `m` links of a
  colour `j` carry link-influence at least `T` (the *local* KKL hypothesis on each
  link), then some global colour `i ≠ j` has influence at least the average
  `mT/(n-1)`.
* `abstract_localToGlobal_KKL` / `abstract_global_influential_coord` — the abstract
  weighted-averaging engine behind every such argument, and
  `partite_total_via_abstract` exhibiting the partite complex as an instance.
* `partite_localKKL_influential_coord_real` — the real-valued averaged form.
* `zero_influence_constant` — the exact converse boundary: a labelling all of whose
  colour influences vanish is constant, so the KKL conclusion is vacuous precisely
  for the degenerate (constant) labellings.
-/

open PartiteKKL

open Finset

/-! ## The complete `n`-partite complex over the alphabet `Fin m` -/


variable {n m : ℕ}









/-! ### Pigeonhole -/





/-! ## Abstract engine: local KKL ⟹ global KKL -/







/-! ## The partite complex as an instance of the abstract engine -/


/-! ## Real-valued averaged global influential coordinate -/


/-! ## The degenerate boundary: vanishing influence forces constancy -/




/-
-- !-- Lab Notes -- !--

**Hypothesis.**  The Kahn–Kalai–Linial influence theorem is a *local* statement on
a single Boolean function.  We conjectured a *local-to-global* upgrade: on a
complex whose links each satisfy a KKL-type influence lower bound, the whole
complex inherits a global KKL-type bound.  The Boolean cube is the two-symbol case;
we conjectured the correct engine is alphabet-independent, driven by an exact
self-averaging identity for influences over the links of any single coordinate.

**Experiment.**  We modelled the complete `n`-partite complex with parts of size
`m`: its facets are transversals `Fin n → Fin m`, and the links of a colour `j`
are its `m` value-pinned subcomplexes.  Defining influence as the count of
sensitive Hamming edges, we tested and then proved the bridge identity
`inf_decomp : Inf f i = ∑ b, InfSub f j b i` by fibering the sensitive-edge set
over the pinned value.  Summing over colours (`linktot_decomp`) and pigeonholing
(`exists_ge_avg_nat`) gave the flagship `localToGlobal_KKL_partite`.  We further
abstracted the mechanism to an arbitrary weighted family of links
(`abstract_localToGlobal_KKL`) and showed the partite complex is a unit-weight
instance (`partite_total_via_abstract`).

**Analysis.**  The single load-bearing fact is that a coordinate influence is an
*exact* (not merely approximate) average of link influences; every downstream
bound is a pigeonhole over that identity.  The `m`-fold link structure — absent in
the classical two-symbol cube — strengthens the total-influence lower bound from
`2T` to `mT`, so richer alphabets propagate more influence to the global level.
The averaging argument never used `m = 2`, `Bool`, or any metric structure; it used
only non-negativity and finiteness, which is why it lifts verbatim to the abstract
weighted engine.

**Critique.**  A KKL-style conclusion is vacuous for degenerate (constant)
labellings, so we pinned down that boundary exactly: `zero_influence_constant`
shows a labelling with all influences zero is constant, i.e. the only obstruction
to a globally influential coordinate is genuine degeneracy — precisely what the
lower-bound hypotheses of the main theorem exclude.  This rules out a vacuous
reading of the flagship statement.

**Synthesis.**  A single exact averaging identity for influences over the links of
one coordinate yields, uniformly across all alphabets, a local-to-global KKL
theorem; the classical Boolean cube is the `m = 2` shadow of a genuinely
alphabet-graded phenomenon.
-/
open PartiteKKL in
theorem solution{n m : ℕ} (f : (Fin n → Fin m) → Bool)
    (h : ∀ i, Inf f i = 0) (x y : Fin n → Fin m) : f x = f y := by
  -- Induct on the set of coordinates where `x` and `y` differ, flipping one at a time.
  have h_ind : ∀ (s : Finset (Fin n)), (∀ i ∈ s, x i ≠ y i) →
      (∀ i ∉ s, x i = y i) → f x = f y := by
    intro s hs hs'
    induction' s using Finset.induction with i s hi ih generalizing x y
    · rw [show x = y from funext fun k => hs' k (by simp)]
    · -- Flip coordinate `i` of `x` to `y i`; this leaves the labelling unchanged.
      have hflip : f x = f (Function.update x i (y i)) :=
        eq_of_inf_zero f i (h i) x (Function.update x i (y i))
          (fun k hk => by rw [Function.update_of_ne hk])
      -- The flipped point agrees with `y` on `i` and differs from `y` only within `s`.
      have htail : f (Function.update x i (y i)) = f y := by
        grind +extAll
      rw [hflip, htail]
  exact h_ind (Finset.univ.filter fun i => x i ≠ y i) (by aesop) (by aesop)
