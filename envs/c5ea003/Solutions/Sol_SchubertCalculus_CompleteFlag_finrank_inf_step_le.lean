-- Prove2me | solution 1 for SchubertCalculus.CompleteFlag.finrank_inf_step_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:54:44.750423+00:00
-- url     : https://prove2.me/submissions/deb3369a-ca46-4b3f-a97b-9c3f00d639c8

-- Sol generated from Geometry/SchubertCalculus/Flags.lean
import Mathlib
import Definitions.Def_Geometry_SchubertCalculus_Flags
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Schubert calculus I: complete flags, jump sequences and the cell decomposition

This file provides rigorous foundations for the combinatorial skeleton of the Grassmannian
that underlies Schubert's enumerative calculus.

Given a complete flag `0 = F₀ ⊂ F₁ ⊂ ⋯ ⊂ Fₙ = V` in an `n`-dimensional vector space and a
`k`-dimensional subspace `W ≤ V`, the *jump set*
`J(W) = {i < n | dim (W ⊓ Fᵢ₊₁) = dim (W ⊓ Fᵢ) + 1}` is the fundamental discrete invariant.

Main results:

* `SchubertCalculus.CompleteFlag.finrank_inf_step_le` : the dimension of `W ⊓ Fᵢ` grows by at
  most one at each step (a rank–nullity argument through the one dimensional quotient
  `Fᵢ₊₁ / Fᵢ`);
* `SchubertCalculus.CompleteFlag.finrank_inf_eq_card_jumpSet` : `dim (W ⊓ F_j)` equals the
  number of jumps below `j` — the exact "Schubert dimension datum" of `W`;
* `SchubertCalculus.CompleteFlag.card_jumpSet` : the jump set has exactly `k = dim W` elements,
  so that jump sets are indexed by `k`-element subsets of `{0, …, n-1}`;
* `SchubertCalculus.CompleteFlag.cell_pairwise_disjoint` /
  `SchubertCalculus.CompleteFlag.mem_cell_jumpSet` : the Schubert cells partition the
  Grassmannian.

Everything is stated for an arbitrary field and an arbitrary complete flag.
-/

open SchubertCalculus

open Module Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]


open CompleteFlag

variable {n : ℕ} (Fl : CompleteFlag K V n)



variable [FiniteDimensional K V] (W : Submodule K V)



















open SchubertCalculus in
theorem solution{i : ℕ} (hi : i < n) :
    finrank K ((W ⊓ Fl.part (i + 1) : Submodule K V)) ≤
      finrank K ((W ⊓ Fl.part i : Submodule K V)) + 1 := by
  set A : Submodule K V := W ⊓ Fl.part (i + 1) with hA
  have hAi : A ⊓ Fl.part i = W ⊓ Fl.part i := by
    rw [hA, inf_assoc, inf_eq_right.2 (Fl.mono (Nat.le_succ i))]
  have hsup : A ⊔ Fl.part i ≤ Fl.part (i + 1) :=
    sup_le inf_le_right (Fl.mono (Nat.le_succ i))
  have key := Submodule.finrank_sup_add_finrank_inf_eq A (Fl.part i)
  have h1 : finrank K (Fl.part i) = i := Fl.finrank_part i hi.le
  have h2 : finrank K (Fl.part (i + 1)) = i + 1 := Fl.finrank_part (i + 1) hi
  have h3 : finrank K ((A ⊔ Fl.part i : Submodule K V)) ≤ i + 1 := by
    rw [← h2]; exact Submodule.finrank_mono hsup
  rw [hAi, h1] at key
  omega
