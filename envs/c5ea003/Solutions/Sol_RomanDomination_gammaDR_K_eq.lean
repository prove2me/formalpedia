-- Prove2me | solution 1 for RomanDomination.gammaDR_K_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:45:22.548962+00:00
-- url     : https://prove2.me/submissions/742da7f5-5810-4435-98c8-231f3d7665f0

-- Sol generated from Geometry/RomanDomination/DoubleRoman.lean
import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_DoubleRoman
import Definitions.Def_Geometry_RomanDomination_Variants
import Theorems.Thm_RomanDomination_K_adj_inl_inr
import Theorems.Thm_RomanDomination_K_adj_inr_inl
import Theorems.Thm_RomanDomination_exists_gammaDR
import Theorems.Thm_RomanDomination_four_le_weight_of_isDRDF_K
import Theorems.Thm_RomanDomination_gammaDR_le
import Theorems.Thm_RomanDomination_isDRDF_swap
import Theorems.Thm_RomanDomination_six_le_weight_of_isDRDF_K
import Theorems.Thm_RomanDomination_three_le_weight_of_isDRDF
import Theorems.Thm_RomanDomination_weight_sum_type
/-
# The double Roman domination number of the complete bipartite graph

This file computes `γ_dR(K_{m,n})` exactly for all `m, n ≥ 1`.  Writing
`k = min m n`, the answer is

```
γ_dR(K_{m,n}) = 3   if k = 1,
              = 4   if k = 2,
              = 6   if k ≥ 3.
```

Note that this is *not* of the shape `min 6 (k + 2)`: the value jumps from `4`
to `6`, skipping `5`.

The lower bounds are obtained from the local conditions defining a double Roman
dominating function, applied to a `0`-labelled vertex on each side; the upper
bounds come from three explicit labellings (`3` on the unique left vertex,
`2` on both left vertices, and `3` on one vertex of each side).

Along the way we prove the general bound `3 ≤ γ_dR(G)` for every graph with at
least two vertices.
-/


open RomanDomination

open Finset

/-! ### General weight plumbing -/


variable {α : Type*} [Fintype α] [DecidableEq α] {g : α → ℕ}





/-! ### The general lower bound `3 ≤ γ_dR(G)` -/


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]




omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Lower bounds on `γ_dR` are proved by bounding the weight of every double Roman
dominating function. -/
lemma le_gammaDR {k : ℕ} (h : ∀ f : V → ℕ, IsDRDF G f → k ≤ weight f) : k ≤ gammaDR G := by
  obtain ⟨f, hf, hw⟩ := exists_gammaDR G
  exact hw ▸ h f hf

omit [DecidableRel G.Adj] in
/-- **`γ_dR(G) ≥ 3`** for every graph with at least two vertices. -/
theorem three_le_gammaDR (hV : 2 ≤ Fintype.card V) : 3 ≤ gammaDR G :=
  le_gammaDR fun _ hf => three_le_weight_of_isDRDF hV hf


/-! ### Local consequences of the double Roman conditions on `K_{m,n}` -/


variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}














/-! ### Explicit double Roman dominating functions of `K_{m,n}` -/


variable {m n : ℕ}




lemma weight_leftThree : weight (leftThree n) = 3 := by
  simp [weight_sum_type, leftThree]

lemma weight_leftTwos : weight (leftTwos m n) = 2 * m := by
  simp [weight_sum_type, leftTwos, mul_comm]

lemma weight_cornerThree (hm : 1 ≤ m) (hn : 1 ≤ n) : weight (cornerThree m n) = 6 := by
  simp [weight_sum_type, cornerThree]
  have hleft : ∑ i : Fin m, (if i.val = 0 then 3 else 0) = 3 := by
    rw [Finset.sum_eq_single ⟨0, hm⟩] <;> simp [Fin.ext_iff]
  have hright : ∑ j : Fin n, (if j.val = 0 then 3 else 0) = 3 := by
    rw [Finset.sum_eq_single ⟨0, hn⟩] <;> simp [Fin.ext_iff]
  omega

lemma isDRDF_leftThree : IsDRDF (K 1 n) (leftThree n) := by
  refine ⟨fun v => by cases v <;> simp [leftThree], fun v h0 => ?_, fun v h1 => ?_⟩
  · cases v with
    | inl i => simp [leftThree] at h0
    | inr j =>
      exact Or.inl ⟨Sum.inl ⟨0, by norm_num⟩, K_adj_inr_inl j ⟨0, by norm_num⟩,
        by simp [leftThree]⟩
  · cases v with
    | inl i => simp [leftThree] at h1
    | inr j => simp [leftThree] at h1

lemma isDRDF_leftTwos (hm : 2 ≤ m) : IsDRDF (K m n) (leftTwos m n) := by
  refine ⟨fun v => by cases v <;> simp [leftTwos], fun v h0 => ?_, fun v h1 => ?_⟩
  · cases v with
    | inl i => simp [leftTwos] at h0
    | inr j =>
      refine Or.inr ⟨Sum.inl ⟨0, by omega⟩, Sum.inl ⟨1, by omega⟩, by simp,
        K_adj_inr_inl j ⟨0, by omega⟩, K_adj_inr_inl j ⟨1, by omega⟩, le_rfl, le_rfl⟩
  · cases v with
    | inl i => simp [leftTwos] at h1
    | inr j => simp [leftTwos] at h1

lemma isDRDF_cornerThree (hm : 1 ≤ m) (hn : 1 ≤ n) : IsDRDF (K m n) (cornerThree m n) := by
  refine ⟨fun v => by cases v <;> simp [cornerThree] <;> split_ifs <;> norm_num,
    fun v _ => ?_, fun v h1 => ?_⟩
  · cases v with
    | inl i => exact Or.inl ⟨Sum.inr ⟨0, hn⟩, K_adj_inl_inr i ⟨0, hn⟩, by simp [cornerThree]⟩
    | inr j => exact Or.inl ⟨Sum.inl ⟨0, hm⟩, K_adj_inr_inl j ⟨0, hm⟩, by simp [cornerThree]⟩
  · cases v with
    | inl i => simp [cornerThree] at h1; (split_ifs at h1; omega)
    | inr j => simp [cornerThree] at h1; (split_ifs at h1; omega)


/-! ### Lower bounds for `K_{m,n}` -/


variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}








/-! ### Exact values -/


variable {m n : ℕ}


lemma weight_swap (f : Fin m ⊕ Fin n → ℕ) :
    weight (fun x : Fin n ⊕ Fin m => f x.swap) = weight f := by
  simp [weight]
  ring

/-- The double Roman domination number is symmetric in the two sides. -/
theorem gammaDR_K_comm : gammaDR (K m n) = gammaDR (K n m) := by
  refine le_antisymm (le_gammaDR fun f hf => ?_) (le_gammaDR fun f hf => ?_)
  · have hweight := @weight_swap n m f
    simp only at hweight
    exact hweight ▸ gammaDR_le (G := K m n) (@isDRDF_swap n m f hf)
  · exact weight_swap f ▸ gammaDR_le (G := K n m) (isDRDF_swap hf)

/-- **`γ_dR(K_{1,n}) = 3`.** -/
theorem gammaDR_K_one (hn : 1 ≤ n) : gammaDR (K 1 n) = 3 := by
  refine le_antisymm (weight_leftThree ▸ gammaDR_le _ isDRDF_leftThree) (three_le_gammaDR ?_)
  simp [Fintype.card_sum]
  omega

/-- **`γ_dR(K_{2,n}) = 4` for `n ≥ 2`.** -/
theorem gammaDR_K_two (hn : 2 ≤ n) : gammaDR (K 2 n) = 4 := by
  refine le_antisymm ?_ ?_
  · have h : weight (leftTwos (2 : ℕ) n) = 4 := by simp [weight_leftTwos]
    exact h ▸ gammaDR_le _ (isDRDF_leftTwos (by omega))
  · exact le_gammaDR fun f hf => four_le_weight_of_isDRDF_K (by omega : 2 ≤ (2 : ℕ)) hn hf

/-- **`γ_dR(K_{m,n}) = 6` for `m, n ≥ 3`.** -/
theorem gammaDR_K_three (hm : 3 ≤ m) (hn : 3 ≤ n) : gammaDR (K m n) = 6 :=
  le_antisymm
    ((gammaDR_le _ (isDRDF_cornerThree (by omega) (by omega))).trans_eq
      (weight_cornerThree (by omega) (by omega)))
    (le_gammaDR fun _ hf => six_le_weight_of_isDRDF_K hm hn hf)




open RomanDomination in
theorem solution(hm : 1 ≤ m) (hn : 1 ≤ n) :
    gammaDR (K m n) = if min m n = 1 then 3 else if min m n = 2 then 4 else 6 := by
  by_cases h1 : min m n = 1
  · simp [h1]
    have hmn : m = 1 ∨ n = 1 := by omega
    rcases hmn with rfl | rfl
    · exact gammaDR_K_one hn
    · rw [gammaDR_K_comm]; exact gammaDR_K_one hm
  · simp [h1]
    by_cases h2 : min m n = 2
    · simp [h2]
      have hmn : m = 2 ∨ n = 2 := by omega
      rcases hmn with rfl | rfl
      · exact gammaDR_K_two (by omega : 2 ≤ n)
      · rw [gammaDR_K_comm]; exact gammaDR_K_two (by omega : 2 ≤ m)
    · simp [h2]
      have hm3 : 3 ≤ m := by omega
      have hn3 : 3 ≤ n := by omega
      exact gammaDR_K_three hm3 hn3
