-- Prove2me | solution 1 for HypercubeNoStretch.HammingDist_flip
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:17:33.98292+00:00
-- url     : https://prove2.me/submissions/8a979e4d-8bf0-4242-acaa-f9d4e7412438

-- Sol generated from Applications/Combinatorics/HypercubeNoStretch.lean
import Mathlib
import Definitions.Def_Applications_Combinatorics_HypercubeNoStretch

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















variable {V : Type*} {G : SimpleGraph V} {k : ℕ} {ℓ : V → Cube k}




theorem solution{k : ℕ} (x y : Cube k) (i : Fin k) (hi : x i ≠ y i) :
    HammingDist (flipCoord x i) y + 1 = HammingDist x y := by
  have hyi : y i = x i + 1 := by
    have : ∀ a b : ZMod 2, a ≠ b → b = a + 1 := by decide
    exact this _ _ hi
  unfold HammingDist flipCoord
  have hset : (Finset.univ.filter (fun j => Function.update x i (x i + 1) j ≠ y j))
      = (Finset.univ.filter (fun j => x j ≠ y j)).erase i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      Function.update_apply]
    by_cases hj : j = i
    · subst hj; simp [hyi]
    · simp [hj]
  rw [hset, Finset.card_erase_of_mem (by simp [hi])]
  have hmem : i ∈ Finset.univ.filter (fun j => x j ≠ y j) := by simp [hi]
  have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
  omega
