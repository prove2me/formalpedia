-- Prove2me | Definitions.Def_Cryptography_BerggrenTrees_BerggrenFreeMonoid
-- name    : Cryptography_BerggrenTrees_BerggrenFreeMonoid
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:11:53.788596+00:00
-- url     : https://prove2.me/theorems/cc334ed5-3ea2-4904-b8ff-d353a351a9f9
-- title:
--   Aether Catalog definitions — Cryptography_BerggrenTrees_BerggrenFreeMonoid
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BerggrenTrees.BerggrenFreeMonoid`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BerggrenTrees/BerggrenFreeMonoid.lean by skeleton subtraction
import Mathlib

/-!
# Berggren Free Monoid: Unique Factorization and Word-Metric Rigidity

We prove that the three Berggren generators, realized as 2×2 integer matrices,
generate a **free semigroup** of rank 3 inside `GL₂(ℤ)`.

## Main Results

* `evalBergWord_injective` — the matrix evaluation map is injective (freeness)
* `evalBergWord_eq_iff` — equal matrix products ↔ equal words
* `bergWordOf_unique` — unique coding of semigroup elements
* `leftDivides_iff_prefix` / `rightDivides_iff_suffix` — divisibility = prefix/suffix
* `bergLength_mul` — word length is additive
* `eval_prefix_rigidity` — equal-length prefixes of equal products agree
* `berg_overlap_free_monoid` — free-monoid overlap theorem
* `equal_products_prefix_comparable` — prefix comparability of left factors
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Generator Type -/

/-- The three Berggren generators. -/
inductive BergGen : Type
  | A | B | C
  deriving DecidableEq, Repr

instance : Fintype BergGen where
  elems := {.A, .B, .C}
  complete := by intro x; cases x <;> simp

/-- A Berggren word is a list of generators. -/
abbrev BergWord := List BergGen

/-! ## Pair-Based Evaluation -/

def actGen (g : BergGen) (p : ℤ × ℤ) : ℤ × ℤ :=
  match g with
  | .A => (2 * p.1 - p.2, p.1)
  | .B => (2 * p.1 + p.2, p.1)
  | .C => (p.1 + 2 * p.2, p.2)

def rootPair : ℤ × ℤ := (2, 1)

def evalPair : BergWord → ℤ × ℤ
  | [] => rootPair
  | g :: rest => actGen g (evalPair rest)

def ValidPair (p : ℤ × ℤ) : Prop := 0 < p.2 ∧ p.2 < p.1










/-! ## Matrix Formulation -/

def bergMat : BergGen → Matrix (Fin 2) (Fin 2) ℤ
  | .A => !![2, -1; 1, 0]
  | .B => !![2, 1; 1, 0]
  | .C => !![1, 2; 0, 1]

def evalBergWord : BergWord → Matrix (Fin 2) (Fin 2) ℤ
  | [] => 1
  | g :: rest => bergMat g * evalBergWord rest



def pairOfMat (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ × ℤ :=
  (2 * M 0 0 + M 0 1, 2 * M 1 0 + M 1 1)




/-! ## Unique Coding -/

def InBergSemigroup (M : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∃ w : BergWord, evalBergWord w = M

noncomputable def bergWordOf (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : InBergSemigroup M) :
    BergWord := hM.choose




/-! ## Non-triviality -/



/-! ## Divisibility -/

def LeftDivides (X Y : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∃ Z, InBergSemigroup Z ∧ Y = X * Z

def RightDivides (X Y : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∃ Z, InBergSemigroup Z ∧ Y = Z * X







/-! ## Additive Word Length -/

noncomputable def bergLength (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : InBergSemigroup M) : ℕ :=
  (bergWordOf M hM).length





/-! ## Cancellation -/




/-! ## Prefix Rigidity -/


/-! ## Overlap Decomposition -/


