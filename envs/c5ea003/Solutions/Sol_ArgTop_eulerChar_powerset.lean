-- Prove2me | solution 1 for ArgTop.eulerChar_powerset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T16:49:34.481931+00:00
-- url     : https://prove2.me/submissions/413a69ea-bf09-44aa-ace5-38bbf1fa5716

-- Sol generated from Novelty/ArgumentationSimplicial.lean
import Mathlib
import Definitions.Def_Novelty_ArgumentationSimplicial

/-!
# The topology of argumentation, III: the simplicial complex `K(AF)` and its Euler characteristic

This file is **self-contained**.  It makes precise the central geometric claim
about argumentation frameworks and settles the associated Euler-characteristic
conjecture.

## The complex `K(AF)`

For an argumentation framework `(A, R)` the *conflict-free* subsets of `A` are
**downward closed**: any subset of a conflict-free set is conflict-free.  This is
exactly the defining axiom of an *abstract simplicial complex*.  We record this
as `conflictFreeComplex R : ASC A`.  (Note: it is the **conflict-free sets**, not
the preferred extensions, that form the complex — preferred extensions are the
*maximal* admissible sets and are not downward closed, so the naive reading of
the informal conjecture does not typecheck; `conflictFreeComplex` is the correct
carrier of the topology.)

## Euler characteristic

`eulerChar F` is the (unreduced) Euler characteristic of a finite family of
faces, `∑_{∅ ≠ s ∈ F} (-1)^(dim s)` with `dim s = |s| - 1`.  We prove
`eulerChar_powerset`: the full simplex on a nonempty vertex set is contractible
(`χ = 1`), and empty otherwise.

## The Euler = semantics conjecture is false

The informal conjecture asserts

  `χ(K(AF)) = |preferred extensions| − |grounded extension|`.

We refute it with an explicit witness: the attack-free framework on a single
argument (`R0` on `Fin 1`).  There `χ(K) = 1` (a point), there is exactly one
preferred extension, and the grounded extension has size `1`, so the right-hand
side is `1 − 1 = 0 ≠ 1`.  See `euler_semantics_conjecture_false`.
-/

open ArgTop

open Finset

variable {A : Type*}










/-!
## Refuting the Euler = semantics conjecture

We now set up the machinery needed to state the conjecture (`Defends`,
`Admissible`, `Preferred`, `groundedExt`) and produce the explicit
counterexample.
-/



















open ArgTop in
theorem solution[DecidableEq A] (X : Finset A) :
    eulerChar (X.powerset) = if X = ∅ then 0 else 1 := by
  unfold eulerChar
  have key : ∀ s : Finset A, (if s = ∅ then (0 : ℤ) else (-1) ^ (s.card - 1))
      = -((-1) ^ s.card) + (if s = ∅ then 1 else 0) := by
    intro s
    by_cases hs : s = ∅
    · simp [hs]
    · have hc : 1 ≤ s.card := Finset.one_le_card.mpr (Finset.nonempty_of_ne_empty hs)
      rw [if_neg hs, if_neg hs]
      have h2 : s.card - 1 + 1 = s.card := Nat.sub_add_cancel hc
      calc (-1 : ℤ) ^ (s.card - 1) = -((-1) ^ (s.card - 1) * (-1)) := by ring
        _ = -((-1) ^ (s.card - 1 + 1)) := by rw [pow_succ]
        _ = -((-1) ^ s.card) + 0 := by rw [h2]; ring
  rw [Finset.sum_congr rfl (fun s _ => key s), Finset.sum_add_distrib,
      Finset.sum_neg_distrib, Finset.sum_powerset_neg_one_pow_card]
  have hemp : ∑ s ∈ X.powerset, (if s = ∅ then (1 : ℤ) else 0) = 1 := by
    rw [Finset.sum_ite_eq' X.powerset ∅ (fun _ => (1 : ℤ))]; simp
  rw [hemp]; by_cases hX : X = ∅ <;> simp [hX]
