-- Prove2me | Definitions.Def_Geometry_AugmentedConfig29Family
-- name    : Geometry_AugmentedConfig29Family
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:50:54.961087+00:00
-- url     : https://prove2.me/theorems/a90e8788-4b77-43a8-894b-2e4cbee2da48
-- title:
--   Aether Catalog definitions — Geometry_AugmentedConfig29Family
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.AugmentedConfig29Family`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/AugmentedConfig29Family.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_AugmentedConfig29
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The cluster-graph family and unboundedness of `geomFrac`

Companion to `AugmentedConfig29.lean`.  There we exhibited a single 29-vertex model
`G29` with `geomFrac G29 > 4`.  Here we place it in a *family* and extract two
structural consequences of the independence-ratio engine:

* `geomFrac_gt_of_indep_ratio` — the general-threshold reduction: if `k·α(G) < |V|`
  then `geomFrac G > k` (the `k = 4`, `n = 29`, `α = 7` instance is `G29`).
* `clusterGraph` — the general disjoint-union-of-`m`-cliques family on `Fin n`
  (`G29` is `clusterGraph 29 7`); its independence number is `≤ m`, giving
  `k·m < n → geomFrac (clusterGraph n m) > k`.
* `exists_geomFrac_gt` / `geomFrac_unbounded` — the geometric fractional chromatic
  number is **unbounded** across finite graphs (witnessed by complete graphs), so the
  strict regime `geomFrac > 4` of `G29` is one rung of an infinite ladder.
-/
open SimpleGraph Finset
open scoped BigOperators

namespace AugConfig29

variable {V : Type*} [Fintype V] [DecidableEq V]


/-! ## The cluster-graph family -/

/-- The disjoint union of `m` cliques on `Fin n`: two distinct vertices are adjacent
iff congruent mod `m`.  `G29 = clusterGraph 29 7`. -/
def clusterGraph (n m : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (u : ℕ) % m = (v : ℕ) % m
  symm := by rintro u v ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
  loopless := ⟨fun u hu => hu.1 rfl⟩

instance (n m : ℕ) : DecidableRel (clusterGraph n m).Adj := by
  intro u v; unfold clusterGraph; infer_instance

/-
Independent sets of `clusterGraph n m` are `(· % m)`-injective, so have size `≤ m`
(when `m > 0`).
-/

/-
`α(clusterGraph n m) ≤ m` for `m > 0`.
-/


/-! ## Unboundedness of the geometric fractional chromatic number -/


end AugConfig29

/-!
-- !-- Lab Notes -- !--

**Hypothesis (Hypothesizer).**  Bold conjecture: `G29` is not an isolated miracle but
one member of an infinite family, and the independence-ratio engine is powerful
enough to certify `geomFrac > k` for *every* `k`, i.e. the geometric fractional
chromatic number is unbounded across finite graphs.

**Experiment (Experimenter).**  We generalised `G29` to `clusterGraph n m` (disjoint
union of `m` residue-class cliques on `Fin n`) and proved `α ≤ m`
(`clusterGraph_indepNum_le`) by the same pigeonhole injectivity as for `G29`.  The
family reduction `k·m < n → geomFrac > k` (`geomFrac_clusterGraph_gt`) recovers
`G29` at `(n, m, k) = (29, 7, 4)`.  Specialising to `m = 1` (complete graphs) yields
`exists_geomFrac_gt`: for each `k`, `K_{k+1}` has `geomFrac > k`.

**Analysis (Analyst).**  The engine's strength is entirely in the ratio `|V|/α`;
`clusterGraph` lets us dial that ratio to any rational `> 1`, so `geomFrac` takes
arbitrarily large values.  The interesting, hard part of `MRVZ` is *not* achieving
`geomFrac > 4` abstractly (trivial via `K_5`) but doing so with a *unit-distance*
graph — the geometric constraint is what makes `α = 7` on `29` points a theorem
rather than a definition.  This is the honest boundary of the present formalisation.

**Critique (Critic).**  `exists_geomFrac_gt` via complete graphs is deliberately
labelled a *sanity ladder*, not a deep result: it shows the engine is not artificially
capped at `4`.  The genuine content sits in `clusterGraph_indepNum_le` (a real
pigeonhole) and in the `MRVZ` geometric realisation, which remains open here.

**Synthesis (PI).**  Two reusable pieces: the general-`k` reduction
`geomFrac_gt_of_indep_ratio`, and the `clusterGraph` family with its independence
bound.  Together they frame `G29` as the smallest unit-distance-flavoured witness on
an infinite combinatorial ladder.
-/


