-- Prove2me | Definitions.Def_Probability_WignerMomentGrowth
-- name    : Probability_WignerMomentGrowth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:47:01.017034+00:00
-- url     : https://prove2.me/theorems/30109063-9acf-475b-a787-dfae66992f9e
-- title:
--   Aether Catalog definitions — Probability_WignerMomentGrowth
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.WignerMomentGrowth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/WignerMomentGrowth.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
import Definitions.Def_Probability_WignerRademacherEnsemble
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Polynomial growth of every even moment: tightness of the empirical spectral law

`Probability.WignerAllOrderParity` reduces the computation of every trace moment of
the symmetric Rademacher ensemble to a count of *even closed walks* — loop-free
closed walks all of whose edge multiplicities are even — and proves that the odd
moments vanish identically.  This file supplies the missing quantitative half at
even order: an even closed walk of length `2k` can visit at most `k + 1` distinct
vertices, so there are at most `N^(k+1) (k+1)^(2k)` of them and

  `E [ tr (W ^ (2k)) ] ≤ N^(k+1) · (k+1)^(2k)`,
  `E [ (1/N) tr ((W/√N) ^ (2k)) ] ≤ (k+1)^(2k)`   (uniformly in `N`).

The structural core is graph-theoretic and is proved from scratch here:

* `RademacherWigner.card_visited_le` — along any walk, the number of vertices
  visited never exceeds `1 +` the number of distinct edges used (a spanning-tree
  bound, proved by induction on the length of the walk);
* `RademacherWigner.card_edgesUsed_le` — if every edge multiplicity is even, then
  twice the number of distinct edges is at most the length of the walk;
* `RademacherWigner.card_visited_le_of_even` — combining the two, an even closed
  walk of `2k` steps visits at most `k + 1` vertices;
* `RademacherWigner.card_bounded_image_le` — a function `Fin n → Fin N` whose image
  has at most `r` elements is determined by an `r`-element subset together with a
  map into it, giving at most `N^r · r^n` such functions.

Uniform boundedness of all normalised moments is exactly the tightness input of the
moment method: together with `expect_trace_pow_odd` it says that the expected
empirical spectral distribution of `W/√N` has moments that neither blow up nor
oscillate with `N`, at *every* order.
-/

open Matrix BigOperators Finset

namespace RademacherWigner

variable {N : ℕ}

/-! ### Vertices and edges visited by a walk -/

/-- The set of vertices visited by the first `t` steps of the walk `w`. -/
def visited (w : ℕ → Fin N) (t : ℕ) : Finset (Fin N) := (Finset.range (t + 1)).image w

/-- The set of (distinct) edges traversed by the first `t` steps of the walk `w`. -/
def edgesUsed (w : ℕ → Fin N) (t : ℕ) : Finset (Fin N × Fin N) :=
  (Finset.range t).image fun s => edgeOf (w s) (w (s + 1))








/-! ### Counting functions with a small image -/


/-! ### From the `Fin`-indexed encoding of a closed walk to a periodic `ℕ`-walk -/

/-- The `(m+1)`-periodic walk on `ℕ` determined by the base point `i` and the
interior vertices `v`. -/
def cyc (m : ℕ) (i : Fin N) (v : Fin m → Fin N) : ℕ → Fin N := fun t =>
  (Fin.cons i v : Fin (m + 1) → Fin N) ⟨t % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩







/-! ### The count of even closed walks, and the moment bound -/




/-! ### A matching deterministic lower bound -/






end RademacherWigner


