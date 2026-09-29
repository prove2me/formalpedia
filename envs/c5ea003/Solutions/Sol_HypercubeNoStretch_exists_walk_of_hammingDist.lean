-- Prove2me | solution 1 for HypercubeNoStretch.exists_walk_of_hammingDist
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:21:47.058588+00:00
-- url     : https://prove2.me/submissions/5e1fd076-cea8-4982-83c4-afef07daf956

-- Sol generated from Applications/Combinatorics/HypercubeNoStretch.lean
import Mathlib
import Definitions.Def_Applications_Combinatorics_HypercubeNoStretch
import Theorems.Thm_HypercubeNoStretch_HammingDist_flip

/-! # No-stretching for labelings into the hypercube over GF(2)

Let `G` be a connected simple graph on `V`, and `ℓ : V → (Fin k → ZMod 2)` a labeling such that
every `G`-edge `{u,v}` satisfies either `ℓ u = ℓ v` or `HammingDist (ℓ u) (ℓ v) = 1`.

We prove that such a labeling does not stretch distances: the hypercube distance between labels is
bounded by the graph distance.

The hypercube `Q_k` has vertex set `Fin k → ZMod 2` and an edge between two vertices at Hamming
distance `1`.

* `hypercube_dist_eq_hammingDist`: the graph distance in `Q_k` equals the Hamming distance.
* `exists_image_walk`: a `G`-walk maps to a hypercube walk of no greater length.
* `no_stretching`: `(hypercube k).dist (ℓ u) (ℓ v) ≤ G.dist u v`.
-/

open SimpleGraph

open HypercubeNoStretch



lemma HammingDist_comm {k : ℕ} (x y : Cube k) : HammingDist x y = HammingDist y x := by
  unfold HammingDist
  congr 1
  ext i
  simp [ne_comm]

lemma HammingDist_self {k : ℕ} (x : Cube k) : HammingDist x x = 0 := by
  simp [HammingDist]

lemma HammingDist_eq_zero {k : ℕ} {x y : Cube k} : HammingDist x y = 0 ↔ x = y := by
  unfold HammingDist
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h; funext i; have := h (Finset.mem_univ i); simpa using this
  · intro h; subst h; simp



lemma hypercube_adj_iff {k : ℕ} {x y : Cube k} :
    (hypercube k).Adj x y ↔ HammingDist x y = 1 := by
  unfold hypercube
  rw [fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · rwa [HammingDist_comm]
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro hxy; subst hxy; rw [HammingDist_self] at h; exact absurd h (by norm_num)



lemma HammingDist_flip_self {k : ℕ} (x : Cube k) (i : Fin k) :
    HammingDist x (flipCoord x i) = 1 := by
  unfold HammingDist flipCoord
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Function.update_apply]
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]




variable {V : Type*} {G : SimpleGraph V} {k : ℕ} {ℓ : V → Cube k}




theorem solution{k : ℕ} :
    ∀ (n : ℕ) (x y : Cube k), HammingDist x y = n →
      ∃ w : (hypercube k).Walk x y, w.length = n := by
  intro n
  induction n with
  | zero =>
      intro x y h
      obtain rfl := HammingDist_eq_zero.mp h
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ m ih =>
      intro x y h
      -- x ≠ y since HammingDist > 0, so a differing coordinate exists.
      have hxy : x ≠ y := by
        intro hxy; subst hxy; rw [HammingDist_self] at h; exact absurd h (by omega)
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
        by_contra hc; push_neg at hc; exact hxy (funext hc)
      set x' := flipCoord x i with hx'
      have hadj : (hypercube k).Adj x x' := by
        rw [hypercube_adj_iff, hx']; exact HammingDist_flip_self x i
      have hd : HammingDist x' y = m := by
        have := HammingDist_flip x y i hi
        rw [← hx'] at this; omega
      obtain ⟨w', hw'⟩ := ih x' y hd
      exact ⟨SimpleGraph.Walk.cons hadj w', by rw [SimpleGraph.Walk.length_cons, hw']⟩
