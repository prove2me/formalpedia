-- Prove2me | solution 1 for Price2Adic.sum_le_of_length
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:43:00.741799+00:00
-- url     : https://prove2.me/submissions/683ec23b-6094-4ec9-84ee-8a0d7c231ad1

-- Sol generated from Cryptography/Price2Adic/Tree.lean
import Mathlib
import Definitions.Def_Cryptography_Price2Adic_Tree
import Theorems.Thm_Price2Adic_Valid_eval
import Theorems.Thm_Price2Adic_eval_append_one

/-!
# The Price tree of primitive Pythagorean triples: uniqueness and completeness

Price's ternary tree of primitive Pythagorean triples is usually presented by three
`3 × 3` matrices acting on triples `(a,b,c)`.  On the *parameter* side (Euclid's
`(m,n) ↦ (m²-n², 2mn, m²+n²)`) the three moves become the strikingly simple pair maps

* `A : (m,n) ↦ (m+n, 2n)`,
* `B : (m,n) ↦ (2m, m-n)`,
* `C : (m,n) ↦ (2m, m+n)`,

each of which *doubles* one of the two parameters.  This is the "halving alphabet":
every Price move is visible 2-adically, in contrast with the Berggren tree whose
moves are 3-adic in nature (`Catalog/Cryptography/BerggrenTrees`).

This file proves, for these maps, the two facts a brute-force enumeration can only
sample:

* **Well-definedness** (`Valid_step`): each move sends a valid Euclid parameter pair to
  a valid Euclid parameter pair.
* **Uniqueness** (`address_eval`, `eval_injective`): distinct words give distinct nodes —
  the tree has no duplicates.
* **Completeness** (`eval_address`): every valid parameter pair is reached.
* Together: `existsUnique_word` — every primitive Pythagorean triple has exactly one
  Price address; `evalEquiv` packages this as a bijection between Price words and
  valid parameter pairs.

We also prove two-sided *depth* bounds (`sum_le_of_length`, `sum_ge_of_length`)
quantifying that the Price tree grows at most geometrically with ratio `3` and at least
arithmetically with step `2`.  These are the rigorous form of the empirical
"`dP` grows like `log₂(m+n)`" law: the depth of the node `(m,n)` is squeezed
between `log₃(m+n) - 1` and `(m+n-3)/2`.

## Lab notes (round 70, exp 548)

BFS over the parameter tree from the root `(2,1)` to depth `8` produced
`(3^9-1)/2 = 9841` nodes, all distinct (`0` duplicates).  BFS pruned at `c ≤ 5000`
(maximal depth reached: `9`) produced exactly `792` nodes, matching a brute-force
enumeration of the primitive triples with `c ≤ 5000` with `0` missing and `0` extra.
The theorems below replace both finite checks by proofs.  The child triples of
`(3,4,5)` are `(5,12,13)`, `(15,8,17)`, `(7,24,25)` (`triple_children_root`), i.e. this
is the Price tree and not Berggren's, whose root children include `(21,20,29)`.
-/

open Price2Adic

/-! ## Arithmetic helpers -/




/-! ## The alphabet, the moves, and the nodes -/
















/-! ## Well-definedness -/



/-! ## The letter and the parent of a node -/









/-! ## Addresses: uniqueness and completeness -/





theorem sum_step_le (l : PriceLetter) (p : ℕ × ℕ) (hp : Valid p) :
    (step l p).1 + (step l p).2 ≤ 3 * (p.1 + p.2) := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, -, -⟩ := hp
  cases l <;> simp only [step] <;> omega










/-! ## Depth bounds (the rigorous `dP` law) -/





open Price2Adic in
theorem solution(w : PriceWord) : (eval w).1 + (eval w).2 ≤ 3 ^ (w.length + 1) := by
  induction w using List.reverseRecOn with
  | nil => norm_num [eval, root]
  | append_singleton t l ih =>
    rw [eval_append_one]
    calc (step l (eval t)).1 + (step l (eval t)).2 ≤ 3 * ((eval t).1 + (eval t).2) :=
          sum_step_le l _ (Valid_eval t)
      _ ≤ 3 * 3 ^ (t.length + 1) := by omega
      _ = 3 ^ ((t ++ [l]).length + 1) := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          ring
