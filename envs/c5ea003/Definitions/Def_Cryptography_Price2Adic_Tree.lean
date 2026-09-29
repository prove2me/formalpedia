-- Prove2me | Definitions.Def_Cryptography_Price2Adic_Tree
-- name    : Cryptography_Price2Adic_Tree
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:21:49.7474+00:00
-- url     : https://prove2.me/theorems/b0f24f2e-bc9e-4488-9720-be77a8844052
-- title:
--   Aether Catalog definitions — Cryptography_Price2Adic_Tree
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.Price2Adic.Tree`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/Price2Adic/Tree.lean by skeleton subtraction
import Mathlib

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

namespace Price2Adic

/-! ## Arithmetic helpers -/




/-! ## The alphabet, the moves, and the nodes -/

/-- The three letters of the Price alphabet. -/
inductive PriceLetter : Type
  | A | B | C
  deriving DecidableEq, Repr

/-- A Price word: a path from the root, read left to right. -/
abbrev PriceWord := List PriceLetter

/-- Euclid parameter pairs generating *primitive* Pythagorean triples:
`0 < n < m`, `gcd m n = 1`, and `m + n` odd. -/
def Valid : ℕ × ℕ → Prop
  | (m, n) => 0 < n ∧ n < m ∧ Nat.gcd m n = 1 ∧ (m + n) % 2 = 1

instance : DecidablePred Valid := fun p => by
  obtain ⟨m, n⟩ := p; unfold Valid; infer_instance

/-- The three Price moves on parameter pairs. -/
def step : PriceLetter → ℕ × ℕ → ℕ × ℕ
  | .A, (m, n) => (m + n, 2 * n)
  | .B, (m, n) => (2 * m, m - n)
  | .C, (m, n) => (2 * m, m + n)

/-- The root of the Price tree: `(2,1)`, i.e. the triple `(3,4,5)`. -/
def root : ℕ × ℕ := (2, 1)

/-- The node addressed by a Price word. -/
def eval (w : PriceWord) : ℕ × ℕ := w.foldl (fun p l => step l p) root

/-- The Euclid triple attached to a parameter pair. -/
def triple : ℕ × ℕ → ℕ × ℕ × ℕ
  | (m, n) => (m ^ 2 - n ^ 2, 2 * m * n, m ^ 2 + n ^ 2)

/-- The odd leg of the triple attached to a parameter pair. -/
def oddLeg : ℕ × ℕ → ℕ
  | (m, n) => m ^ 2 - n ^ 2







/-! ## Well-definedness -/



/-! ## The letter and the parent of a node -/

/-- The last letter of the address of a node: `A` iff the parameter `n` is even
(the 2-adic reading), and `B`/`C` according to whether `2n < m`. -/
def letterOf : ℕ × ℕ → PriceLetter
  | (m, n) => if n % 2 = 0 then .A else if 2 * n < m then .B else .C

/-- The parent of a node in the Price tree. -/
def parent : ℕ × ℕ → ℕ × ℕ
  | (m, n) =>
      if n % 2 = 0 then (m - n / 2, n / 2)
      else if 2 * n < m then (m / 2, m / 2 - n) else (m / 2, n - m / 2)






theorem parent_sum_lt (p : ℕ × ℕ) (hp : Valid p) (hroot : p ≠ root) :
    (parent p).1 + (parent p).2 < p.1 + p.2 := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, hg, hpar⟩ := hp
  simp only [parent]
  split_ifs <;> simp only <;> omega

/-! ## Addresses: uniqueness and completeness -/

/-- The Price address of a node, computed by iterated `parent`. -/
def address (p : ℕ × ℕ) : PriceWord :=
  if h : Valid p ∧ p ≠ root then
    have : (parent p).1 + (parent p).2 < p.1 + p.2 := parent_sum_lt p h.1 h.2
    address (parent p) ++ [letterOf p]
  else []
termination_by p.1 + p.2














/-! ## Depth bounds (the rigorous `dP` law) -/




end Price2Adic


