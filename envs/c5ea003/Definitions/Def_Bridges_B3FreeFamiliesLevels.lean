-- Prove2me | Definitions.Def_Bridges_B3FreeFamiliesLevels
-- name    : Bridges_B3FreeFamiliesLevels
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:20.760509+00:00
-- url     : https://prove2.me/theorems/ed5c76a0-559d-4c45-b97d-a0ee32567e84
-- title:
--   Aether Catalog definitions — Bridges_B3FreeFamiliesLevels
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.B3FreeFamiliesLevels`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/B3FreeFamiliesLevels.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Level (size-determined) families and the exact level-restricted extremal number

This file continues `Catalog/Bridges/B3FreeFamilies.lean` and
`Catalog/Bridges/B3FreeFamiliesBounds.lean`, which set up the framework of weak/strong
`P`-free families surrounding the paper *On the maximum size of `B_3`-free families*.

The paper's headline result is that `La(n, B_3) ≥ (3 + ε) C(n, ⌊n/2⌋)` for some absolute
`ε > 0`, i.e. that the three-layer construction is *not* optimal.  Here we prove a
complementary structural statement: **no improvement at all can come from a family that is
determined by the sizes of its sets** — equivalently, from a family invariant under the
permutations of the ground set.  Among all such families the `d` central layers are exactly
optimal.

## Main results

* `levelFamily` — the family of all subsets whose size lies in a prescribed set `S` of
  levels, and `card_levelFamily : |𝓛(S)| = ∑_{i ∈ S} C(n, i)`.
* `exists_strongCopy_levelFamily` — if `S` contains `d + 1` levels that are realized in
  `2^[n]`, then `𝓛(S)` contains a *strong* copy of `B_d`.  The levels need **not** be
  consecutive; this generalizes `exists_strongCopy_layers`.
* `levelFamily_weakFree_iff`, `levelFamily_strongFree_iff` — `𝓛(S)` is weak (strong)
  `B_d`-free **iff** at most `d` levels of `S` are realized.
* `sum_choose_le_sum_choose_window` — for a unimodal binomial row, any `d` levels have total
  weight at most that of `d` consecutive levels around the middle.
* `card_levelFamily_le_layers`, `level_extremal` — **exact level-restricted
  extremal number**: a weak `B_d`-free level family has at most `|layers α a d|` sets, for
  the central window `a`, and this is attained.
* `symmetric_weakFree_card_le`, `symmetric_weakFree_card_le_mul` — the same bound for every
  permutation-invariant weak `B_d`-free family, and the clean corollary
  `|F| ≤ d · C(n, ⌊n/2⌋)`: the `ε`-improvement of the paper must break the symmetry of the
  cube.
* `La_boolLat_eq_two_pow_of_lt`, `LaStar_boolLat_eq_two_pow_of_lt` — the degenerate range
  `n < d`, where the whole power set is `B_d`-free.
* `strongFree_boolLatOne_iff`, `LaStar_boolLatOne_eq` — Sperner's theorem also for the
  strong extremal function, `La*(n, B_1) = C(n, ⌊n/2⌋)`.
-/


namespace B3Free

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## Level families -/

/-- The family of all subsets of `α` whose size lies in `S`. -/
def levelFamily (α : Type*) [Fintype α] [DecidableEq α] (S : Finset ℕ) : Finset (Finset α) :=
  {A : Finset α | A.card ∈ S}





/-! ## A weak copy of `B_d` realizes `d + 1` distinct levels -/



/-! ## A strong copy of `B_d` spread over `d + 1` arbitrary levels -/

section Construction

variable {d : ℕ}

/-- The combinatorial index gadget: for `X ⊆ Fin d` the set of positions
`X ∪ [d, d + (t |X| - |X|))` inside `ℕ`, where `t` lists the target levels. -/
private def idxSet (d : ℕ) (t : ℕ → ℕ) (X : BoolLat d) : Finset ℕ :=
  X.image Fin.val ∪ Finset.Ico d (d + (t X.card - X.card))





end Construction


/-! ## Which level families are `B_d`-free -/






/-! ## Unimodality of the binomial row and the optimal window of levels -/



/-- The starting level of the window of `d` consecutive levels centred in the `n`-th
binomial row. -/
def centralStart (n d : ℕ) : ℕ := (n + 1 - d) / 2


/-! ## The level-restricted extremal number -/




/-! ## Permutation-invariant families -/

/-- A family is *symmetric* if it is invariant under the permutations of the ground set. -/
def SymmetricFamily (F : Finset (Finset α)) : Prop :=
  ∀ (e : Equiv.Perm α) (A : Finset α), A ∈ F → A.image e ∈ F








/-! ## Two easy complements -/








end B3Free


