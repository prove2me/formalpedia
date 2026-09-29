-- Prove2me | solution 1 for TheoremNetworks.euler_char_top
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:34:35.763565+00:00
-- url     : https://prove2.me/submissions/ec6050ce-f114-4b64-81c3-88b17e0f9b98

-- Sol generated from Applications/TheoremNetworks/FlagComplex.lean
import Mathlib
import Definitions.Def_Applications_TheoremNetworks_FlagComplex

/-!
# Topological Data Analysis of Theorem Networks: the flag complex and its `f`-vector

This file develops, from first principles over Mathlib, a small self-contained chain of
results about the **flag (clique) complex of a theorem-citation network**.

## Modelling

A *theorem network* is modelled as a finite simple graph `G` on a vertex type `V`:

* vertices of `V` are theorems;
* an edge joins two **co-cited** theorems;
* a triangle joins three mutually co-cited theorems, and so on.

The associated *flag complex* (a.k.a. clique complex) has as its `k`-dimensional faces the
`(k + 1)`-cliques of `G`.  Thus vertices are `1`-cliques, edges are `2`-cliques, filled
triangles are `3`-cliques, etc.  We package the count of `k`-faces as `faceCount G k`.

## The chain of results

Each result feeds into the next:

1. `faceCount_zero` — the `0`-faces (vertices) are exactly the theorems: `faceCount G 0 = #V`.
2. `faceCount_top` — for the **complete** network every subset is a clique, so the number of
   `k`-faces is the binomial coefficient `C(#V, k+1)`.
3. `faceCount_le_top` / `faceCount_le_choose` — an arbitrary network has at most as many faces
   as the complete network, hence `faceCount G k ≤ C(#V, k+1)`.
4. `faceCount_le_pow` — **polynomial upper bound**: `faceCount G k ≤ (#V)^(k+1)`.
5. `faceCount_top_lower` — **polynomial lower bound** for the complete network:
   `(#V - k)^(k+1) ≤ (k+1)! · faceCount ⊤ k`.  Together with (4) this sandwiches the number of
   `k`-faces of the complete network between `(#V - k)^(k+1)/(k+1)!` and `(#V)^(k+1)`, i.e. the
   `f`-vector grows like `n^(k+1)`, where `n = #V`.
6. `euler_char_top` — **Euler characteristic** of the complete network is `1`: the complex is
   contractible.

## Relation to the research conjecture

The mission conjecture asserts that the *Betti numbers* satisfy `β_k ≈ n^(k+1)`.  Result (6)
shows this literal reading is false for the natural "complete co-citation" model: a full simplex
is contractible, so `β₀ = 1` and `β_k = 0` for `k ≥ 1`, and the Euler characteristic is `1`
regardless of `n`.  What genuinely grows like `n^(k+1)` is not the homology but the **`f`-vector**
(the face counts), which is exactly the content of results (4) and (5).  So the provable and
honest form of the conjecture is a statement about the size of the complex, not its homology.
-/

open SimpleGraph Finset

open TheoremNetworks

variable {V : Type*} [Fintype V] [DecidableEq V]




/-- In the complete network every subset is a clique, so the `n`-cliques are all the
`n`-element subsets. -/
lemma cliqueFinset_top (n : ℕ) :
    (⊤ : SimpleGraph V).cliqueFinset n = Finset.univ.powersetCard n := by
  ext s
  rw [SimpleGraph.mem_cliqueFinset_iff, Finset.mem_powersetCard]
  refine ⟨fun h => ⟨Finset.subset_univ _, h.2⟩, ?_⟩
  rintro ⟨-, hcard⟩
  refine ⟨?_, hcard⟩
  intro a ha b hb hab
  rw [SimpleGraph.top_adj]
  rintro rfl
  exact hab rfl

/-- **Face counts of the complete network.** The number of `k`-faces of the complete network
on `n` theorems is the binomial coefficient `C(n, k+1)`. -/
theorem faceCount_top (k : ℕ) :
    faceCount (⊤ : SimpleGraph V) k = (Fintype.card V).choose (k + 1) := by
  rw [faceCount, cliqueFinset_top, Finset.card_powersetCard, Finset.card_univ]







open TheoremNetworks in
theorem solution(hV : 1 ≤ Fintype.card V) :
    ∑ k ∈ Finset.range (Fintype.card V),
      ((-1 : ℤ)) ^ k * (faceCount (⊤ : SimpleGraph V) k : ℤ) = 1 := by
  have key : ∑ m ∈ Finset.range (Fintype.card V + 1),
      ((-1 : ℤ)) ^ m * ((Fintype.card V).choose m : ℤ) = 0 := by
    rw [Int.alternating_sum_range_choose, if_neg (by omega)]
  rw [Finset.sum_range_succ'] at key
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] at key
  have hrw : ∀ k ∈ Finset.range (Fintype.card V),
      ((-1 : ℤ)) ^ (k + 1) * ((Fintype.card V).choose (k + 1) : ℤ)
        = - (((-1 : ℤ)) ^ k * (faceCount (⊤ : SimpleGraph V) k : ℤ)) := by
    intro k _
    rw [faceCount_top]
    ring
  rw [Finset.sum_congr rfl hrw, Finset.sum_neg_distrib] at key
  linarith
