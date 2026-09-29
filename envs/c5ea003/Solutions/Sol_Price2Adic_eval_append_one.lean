-- Prove2me | solution 1 for Price2Adic.eval_append_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:33:54.043077+00:00
-- url     : https://prove2.me/submissions/5f2f098d-7afa-4b3f-b5b5-58f02b39433e

-- Sol generated from Cryptography/Price2Adic/Tree.lean
import Mathlib
import Definitions.Def_Cryptography_Price2Adic_Tree

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















/-! ## Depth bounds (the rigorous `dP` law) -/





open Price2Adic in
theorem solution(w : PriceWord) (l : PriceLetter) :
    eval (w ++ [l]) = step l (eval w) := by
  simp [eval]
