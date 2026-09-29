-- Prove2me | solution 1 for HypercubeNoStretch.exists_image_walk
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:17:34.440425+00:00
-- url     : https://prove2.me/submissions/4c0965b7-32ea-460c-96d1-8dffc44e7458

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



lemma HammingDist_comm {k : ℕ} (x y : Cube k) : HammingDist x y = HammingDist y x := by
  unfold HammingDist
  congr 1
  ext i
  simp [ne_comm]

lemma HammingDist_self {k : ℕ} (x : Cube k) : HammingDist x x = 0 := by
  simp [HammingDist]




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







variable {V : Type*} {G : SimpleGraph V} {k : ℕ} {ℓ : V → Cube k}




theorem solution    (hℓ : ∀ {u v : V}, G.Adj u v → ℓ u = ℓ v ∨ HammingDist (ℓ u) (ℓ v) = 1)
    {u v : V} (w : G.Walk u v) :
    ∃ w' : (hypercube k).Walk (ℓ u) (ℓ v), w'.length ≤ w.length := by
  induction w with
  | nil => exact ⟨SimpleGraph.Walk.nil, le_rfl⟩
  | @cons a b c h p ih =>
      obtain ⟨w', hw'⟩ := ih
      rcases hℓ h with heq | hone
      · -- ℓ a = ℓ b: reuse the walk from ℓ b to ℓ c, transported to start at ℓ a.
        refine ⟨w'.copy heq.symm rfl, ?_⟩
        rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_cons]
        omega
      · -- HammingDist (ℓ a) (ℓ b) = 1: prepend a single hypercube edge.
        have hadj : (hypercube k).Adj (ℓ a) (ℓ b) := hypercube_adj_iff.mpr hone
        refine ⟨SimpleGraph.Walk.cons hadj w', ?_⟩
        rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons]
        omega
