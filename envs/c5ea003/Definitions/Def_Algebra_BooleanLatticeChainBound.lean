-- Prove2me | Definitions.Def_Algebra_BooleanLatticeChainBound
-- name    : Algebra_BooleanLatticeChainBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:07:46.37902+00:00
-- url     : https://prove2.me/theorems/71ed9955-8e5b-4dfd-ac96-b25ebd1766b3
-- title:
--   Aether Catalog definitions — Algebra_BooleanLatticeChainBound
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.BooleanLatticeChainBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/BooleanLatticeChainBound.lean by skeleton subtraction
import Mathlib
/-
# Forbidden Boolean-lattice subposets: the chain bound and its sharpening

This file develops, from scratch, a formal framework for the extremal problem

  `La(n, B_d) = max { |F| : F ⊆ 2^[n], F contains no (weak) copy of the Boolean lattice B_d }`

and proves the classical *chain bound* `La(n, B_d) ≤ (2^d - 1) * C(n, ⌊n/2⌋)`
together with a number of complementary results relevant to the conjecture
`La(n, B_d) ≤ (d + c) * C(n, ⌊n/2⌋)` for an absolute constant `c`.

## Main definitions

* `HasBdCopy d F` : the family `F` of subsets of `Fin n` contains a *weak* copy of the
  `d`-dimensional Boolean lattice, i.e. an injective, containment-preserving map
  `Finset (Fin d) → F`.
* `BdFree d F`    : `F` contains no such copy.
* `HasChain k F`  : `F` contains a strictly increasing chain of `k` sets.
* `La n d`        : the extremal function, the supremum of `|F|` over `B_d`-free `F`.

## Main results

* `hasBdCopy_of_hasChain`    : a chain of `2^d` sets already yields a weak copy of `B_d`.
* `lubell_le_of_no_chain`    : the Lubell mass of a `(k+1)`-chain-free family is at most `k`
  (a Mirsky-type induction feeding into the LYM inequality). This is strictly stronger
  than the corresponding cardinality bound.
* `card_le_of_bdFree`        : the chain bound `|F| ≤ (2^d - 1) * C(n, ⌊n/2⌋)`.
* `La_le_chain_bound`        : `La n d ≤ (2^d - 1) * C(n, ⌊n/2⌋)`.
* `La_one`                   : `La n 1 = C(n, ⌊n/2⌋)` (Sperner's theorem, both directions).
* `La_le_height_bound`       : `La n d ≤ (n+1) * C(n, ⌊n/2⌋)`, hence the conjectured bound
  `(d + 1) * C(n, ⌊n/2⌋)` holds unconditionally whenever `n ≤ d`.
* `La_three_le_four_of_le_eight` : the conjectured `d = 3` bound `La n 3 ≤ 4 * C(n, ⌊n/2⌋)`
  holds for every `n ≤ 8`.
* `La_ge_consecutive_levels` : the lower bound coming from `d` consecutive levels,
  `La n d ≥ ∑_{i=a}^{a+d-1} C(n, i)`.
* `hasBdCopy_succ_of_stacked` and `hasBdCopy_succ_of_parallel_chains` : a *doubling*
  criterion showing that a `B_{d+1}` copy already arises from two "parallel" `B_d` copies,
  a configuration strictly weaker than a single long chain.
-/


namespace Catalog.Algebra.BooleanLatticeChainBound

open Finset

/-! ## The central binomial coefficient -/

/-- The size of the largest layer of the Boolean lattice `2^[n]`. -/
def central (n : ℕ) : ℕ := n.choose (n / 2)



/-! ## Weak copies of the Boolean lattice -/

variable {n : ℕ}

/-- `F` contains a *weak* copy of the `d`-dimensional Boolean lattice `B d`: an injective map
from the subsets of `Fin d` into `F` which preserves containment (not necessarily an induced
subposet). -/
def HasBdCopy (d : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ∃ f : Finset (Fin d) → Finset (Fin n),
    Function.Injective f ∧ (∀ S, f S ∈ F) ∧ ∀ S T : Finset (Fin d), S ⊆ T → f S ⊆ f T

/-- `F` is `B d`-free. -/
def BdFree (d : ℕ) (F : Finset (Finset (Fin n))) : Prop := ¬ HasBdCopy d F

/-- `F` contains a strictly increasing chain of `k` sets. -/
def HasChain (k : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ∃ g : ℕ → Finset (Fin n), (∀ i < k, g i ∈ F) ∧ ∀ i j, i < j → j < k → g i ⊂ g j


/-! ## A linear extension of `B d` -/

instance instFintypeLinearExtension (d : ℕ) : Fintype (LinearExtension (Finset (Fin d))) :=
  inferInstanceAs (Fintype (Finset (Fin d)))

/-- A rank function realising a linear extension of the Boolean lattice `B d`: it is injective,
containment-monotone, and takes values in `{0, …, 2^d - 1}`. -/
noncomputable def rank (d : ℕ) (S : Finset (Fin d)) : ℕ :=
  ((monoEquivOfFin (LinearExtension (Finset (Fin d)))
      (by show Fintype.card (Finset (Fin d)) = 2 ^ d; simp)).symm (toLinearExtension S) : Fin (2 ^ d))




/-! ## Chains produce Boolean-lattice copies -/




/-! ## Mirsky + LYM : the Lubell mass of a chain-free family -/

/-- The Lubell mass `∑_{A ∈ F} 1 / C(n, |A|)` of a family. -/
noncomputable def lubell (F : Finset (Finset (Fin n))) : ℝ :=
  ∑ A ∈ F, ((n.choose A.card : ℝ))⁻¹

/-- The set of maximal members of a family. -/
def maximals (F : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  F.filter (fun A => ∀ B ∈ F, ¬ A ⊂ B)





  




/-! ## The chain bound -/



/-! ## Chains in `2^[n]` have length at most `n+1` -/




/-! ## The extremal function `La` -/

/-- The set of sizes of `B d`-free families in `2^[n]`. -/
def LaSet (n d : ℕ) : Set ℕ := {m | ∃ F : Finset (Finset (Fin n)), BdFree d F ∧ F.card = m}

/-- `La n d` : the maximal size of a `B d`-free family of subsets of `[n]`. -/
noncomputable def La (n d : ℕ) : ℕ := sSup (LaSet n d)










/-! ## `d = 1` : Sperner's theorem -/



/-! ## Lower bounds from consecutive levels -/

/-- The family of all subsets of `[n]` whose size lies in `[a, a+d)`. -/
def levels (n a d : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.Ico a (a + d)).biUnion (fun i => Finset.powersetCard i Finset.univ)








/-! ## The conjecture for `d = 3` in small dimension -/





/-! ## A doubling criterion : `B (d+1)` copies from two parallel `B d` copies -/

/-- Restriction of a subset of `Fin (d+1)` to its first `d` coordinates. -/
def restr {d : ℕ} (U : Finset (Fin (d + 1))) : Finset (Fin d) :=
  Finset.univ.filter (fun i : Fin d => i.castSucc ∈ U)






end Catalog.Algebra.BooleanLatticeChainBound


