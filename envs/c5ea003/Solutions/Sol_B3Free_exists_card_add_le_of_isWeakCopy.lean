-- Prove2me | solution 1 for B3Free.exists_card_add_le_of_isWeakCopy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:16:07.733842+00:00
-- url     : https://prove2.me/submissions/66d884c4-2532-480e-af69-4a2c25586f03

-- Sol generated from Bridges/B3FreeFamilies.lean
import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Weak and strong `P`-free families and the layer number `e(P)`

This file formalizes the basic framework surrounding the paper
*On the maximum size of `B_3`-free families*, and proves the exact value of the
"number of free consecutive layers" invariant for the Boolean lattice posets `B_d`.

## Framework

Following the paper, a family `𝒢` of sets is a **weak copy** of a poset `P` if
there is a bijection `ι : P → 𝒢` with `ι p ⊂ ι q` whenever `p < q`, and a
**strong copy** if moreover `ι p ⊂ ι q` holds *only* when `p < q`.  A family is
weak (strong) `P`-free if it contains no weak (strong) copy of `P`.
`La(n, P)` (`La*(n, P)`) is the maximum size of a weak (strong) `P`-free family
in `2^[n]`.

The poset `B_d` is the Boolean lattice on `d` atoms, formalized here as
`Finset (Fin d)` with the inclusion order (`BoolLat d`).

## Main results

* `layers_weakFree` — any `d` consecutive layers of `2^[n]` are weak `B_d`-free;
  hence `e(B_d) ≥ d` and `La(n, B_d) ≥ ∑ᵢ C(n, i)` over `d` consecutive layers
  (`sum_choose_le_La`).
* `exists_strongCopy_layers` — any `d + 1` consecutive layers of `2^[n]`
  (with enough room, `a + d ≤ n`) contain a *strong* copy of `B_d`.
* `weakFree_layers_iff`, `strongFree_layers_iff` — combining the two: `k`
  consecutive layers are weak (strong) `B_d`-free **iff** `k ≤ d`.  This is the
  statement `e(B_d) = e*(B_d) = d`.
* `La_boolLatOne_eq` — **Sperner's theorem in this language**: `La(n, B_1)` is
  exactly `C(n, ⌊n/2⌋)`, i.e. for `d = 1` the layer construction is optimal and
  no `ε`-improvement is possible.  (The content of the paper is that for `d = 3`,
  in contrast, a positive `ε`-improvement does exist.)
* `La_mono_of_strictMono`, `La_boolLat_mono` — `La` is monotone along strictly
  monotone injections of posets, in particular `La(n, B_d) ≤ La(n, B_(d+1))`.
* `mul_choose_le_La`, `three_mul_choose_le_La_boolLat3` — quantitative forms of the
  layer bound, e.g. `3 · C(n, ⌊n/2⌋ - 2) ≤ La(n, B_3)`.
* `La_lt_two_pow`, `La_boolLat_eq_of_card_eq`, `La_boolLat3_fin3` — `La(n, B_d) < 2^n`
  for `d ≤ n`, with the exact values `La(d, B_d) = 2^d - 1` and `La(3, B_3) = 7`.
* `LaStar_boolLat_eq_of_card_eq`, `La_eq_LaStar_of_card_eq` — the same exact value for the
  strong extremal function, so `La(d, B_d) = La*(d, B_d) = 2^d - 1`.

Maximality of the layer construction, the exact value `La(d+1, B_d) = 2^(d+1) - 2`, and the
general upper bound `La(n, B_d) ≤ (2^d - 1)·C(n, ⌊n/2⌋)` are proved in
`Catalog/Bridges/B3FreeFamiliesBounds.lean`.
-/


open B3Free

open Finset

/-! ## Weak and strong copies -/

variable {α : Type*}









/-! ## Layers of the Boolean lattice -/

variable [DecidableEq α] [Fintype α]





/-! ## The Boolean lattice poset `B_d` -/




/-! ## Strong copies inside `d + 1` layers -/


variable {d : ℕ} (s : Finset α) (f : Fin d → α)









/-! ## The extremal functions `La` and `La*` -/








/-! ## Sperner's theorem: the case `d = 1` -/






/-! ## Monotonicity in the poset, and general bounds -/







/-! ## The case `d = 3`: the setting of the paper -/






/-! ## An exact value: ground set of size exactly `d` -/







open B3Free in
omit [DecidableEq α] [Fintype α] in
theorem solution{d : ℕ} {ι : BoolLat d → Finset α}
    (h : IsWeakCopy ι) : ∃ p q : BoolLat d, (ι p).card + d ≤ (ι q).card := by
  classical
  set S : ℕ → BoolLat d := fun k => Finset.univ.filter (fun i : Fin d => (i : ℕ) < k) with hS
  have hchain : ∀ k, k < d → S k < S (k + 1) := by
    intro k hk
    refine lt_of_le_of_ne ?_ ?_
    · intro i hi
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      omega
    · intro hEq
      have : (⟨k, hk⟩ : Fin d) ∈ S (k + 1) := by
        simp [hS]
      rw [← hEq] at this
      simp [hS] at this
  have key : ∀ k, k ≤ d → (ι (S 0)).card + k ≤ (ι (S k)).card := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 : ι (S n) ⊂ ι (S (n + 1)) := h.2 _ _ (hchain n (by omega))
      have h3 := Finset.card_lt_card h2
      omega
  exact ⟨S 0, S d, key d le_rfl⟩
