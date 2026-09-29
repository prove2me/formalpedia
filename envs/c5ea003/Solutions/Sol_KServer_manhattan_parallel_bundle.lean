-- Prove2me | solution 1 for KServer.manhattan_parallel_bundle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T15:17:23.489284+00:00
-- url     : https://prove2.me/submissions/72f3ab70-7ac3-44f0-9217-6feb8579677d

import Mathlib


/-- `(x, a, b, y)` is a **linear 4-tuple**: the four points occur in this order along a
geodesic, i.e. every consecutive triple satisfies the triangle equality. -/
private def Linear4 {M : Type*} [MetricSpace M] (x a b y : M) : Prop :=
  dist x a + dist a b = dist x b ∧
  dist a b + dist b y = dist a y ∧
  dist x a + dist a y = dist x y ∧
  dist x b + dist b y = dist x y

section SupMetric

variable {d : ℕ}

/-- In the sup metric on `Fin d → ℝ` the distance is attained at some coordinate. -/
private theorem exists_coord_dist (hd : 0 < d) (a b : Fin d → ℝ) :
    ∃ i : Fin d, dist a b = |a i - b i| := by
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fin.pos_iff_nonempty.mp hd
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ
    (fun j => dist (a j) (b j)) hne
  refine ⟨i, le_antisymm ?_ ?_⟩
  · rw [← Real.dist_eq]
    exact (dist_pi_le_iff dist_nonneg).mpr fun j => hi j (Finset.mem_univ j)
  · rw [← Real.dist_eq]
    exact dist_le_pi_dist a b i

/-- The pole of a bundle in direction `i` at height `s`. -/
private def pole (i : Fin d) (s : ℝ) : Fin d → ℝ := fun j => if j = i then s else 0

private theorem pole_apply (i : Fin d) (s : ℝ) (j : Fin d) :
    pole i s j = if j = i then s else 0 := rfl

/-- The distance from a pole is read off the `i`-th coordinate, as soon as that coordinate
dominates all the others. -/
private theorem dist_pole (i : Fin d) (s : ℝ) (a : Fin d → ℝ)
    (h : ∀ j, |a j| ≤ |s - a i|) : dist (pole i s) a = |s - a i| := by
  refine le_antisymm ?_ ?_
  · refine (dist_pi_le_iff (abs_nonneg _)).mpr fun j => ?_
    rw [Real.dist_eq, pole_apply]
    rcases eq_or_ne j i with hj | hj
    · subst hj; simp
    · simp only [if_neg hj, zero_sub, abs_neg]
      exact h j
  · calc |s - a i| = dist (pole i s i) (a i) := by
          rw [Real.dist_eq, pole_apply, if_pos rfl]
      _ ≤ dist (pole i s) a := dist_le_pi_dist _ _ i

/-- **Lemma 5 of Bein–Chrobak–Larmore.** In the sup metric on `Fin d → ℝ`, the pairs of
points of a bounded set whose distance is attained at the coordinate `i` form a *parallel
bundle*: there are two poles `x`, `y` such that every such pair, ordered by its `i`-th
coordinate, sits on a geodesic from `x` to `y`.

Together with `exists_coord_dist`, which assigns to every pair a coordinate realising its
distance, this exhibits any set of pairs as a union of at most `d` parallel bundles — for
`d = 2`, the Manhattan plane, at most two. -/
private theorem parallel_bundle_pole (i : Fin d) (N : ℝ) (hN : 0 ≤ N)
    (S : Set (Fin d → ℝ)) (hS : ∀ a ∈ S, ∀ j, |a j| ≤ N) :
    ∀ a ∈ S, ∀ b ∈ S,
      dist a b = |a i - b i| → b i ≤ a i →
        Linear4 (pole i (2 * N)) a b (pole i (-(2 * N))) := by
  have key : ∀ c : Fin d → ℝ, (∀ j, |c j| ≤ N) →
      dist (pole i (2 * N)) c = 2 * N - c i ∧
      dist (pole i (-(2 * N))) c = 2 * N + c i := by
    intro c hc
    have hci := abs_le.mp (hc i)
    have e1 : |2 * N - c i| = 2 * N - c i := abs_of_nonneg (by linarith [hci.2])
    have e2 : |-(2 * N) - c i| = 2 * N + c i := by
      rw [abs_of_nonpos (by linarith [hci.1])]; ring
    constructor
    · rw [dist_pole i _ c (fun j => by rw [e1]; linarith [hc j, hci.2]), e1]
    · rw [dist_pole i _ c (fun j => by rw [e2]; linarith [hc j, hci.1]), e2]
  intro a ha b hb hab hba
  obtain ⟨hax, hay⟩ := key a (hS a ha)
  obtain ⟨hbx, hby⟩ := key b (hS b hb)
  have hxy : dist (pole i (2 * N)) (pole i (-(2 * N))) = 4 * N := by
    have hpb : ∀ j, |pole i (-(2 * N)) j| ≤ |2 * N - pole i (-(2 * N)) i| := by
      intro j
      rw [pole_apply, pole_apply, if_pos rfl]
      have : |2 * N - -(2 * N)| = 4 * N := by
        rw [abs_of_nonneg (by linarith)]; ring
      rw [this]
      by_cases hj : j = i
      · subst hj; rw [if_pos rfl, abs_of_nonpos (by linarith)]; linarith
      · rw [if_neg hj]; simpa using by linarith
    rw [dist_pole i _ _ hpb, pole_apply, if_pos rfl, abs_of_nonneg (by linarith)]
    ring
  have hd2 : dist a b = a i - b i := by rw [hab, abs_of_nonneg (by linarith)]
  have hay' : dist a (pole i (-(2 * N))) = 2 * N + a i := by rw [dist_comm]; exact hay
  have hby' : dist b (pole i (-(2 * N))) = 2 * N + b i := by rw [dist_comm]; exact hby
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hax, hd2, hbx]; ring
  · rw [hd2, hby', hay']; ring
  · rw [hax, hay', hxy]; ring
  · rw [hbx, hby', hxy]; ring

/-- **Lemma 5 of Bein–Chrobak–Larmore.** In the sup metric on `Fin d → ℝ` — for `d = 2`,
the Manhattan plane — every set of pairs of points of a bounded set is a union of at most
`d` parallel bundles. -/
theorem solution {d : ℕ} (hd : 0 < d) (N : ℝ) (hN : 0 ≤ N)
    (S : Set (Fin d → ℝ)) (hS : ∀ a ∈ S, ∀ j, |a j| ≤ N) :
    ∃ x y : Fin d → (Fin d → ℝ), ∀ a ∈ S, ∀ b ∈ S, ∃ i : Fin d,
      (dist (x i) a + dist a b = dist (x i) b ∧
        dist a b + dist b (y i) = dist a (y i) ∧
        dist (x i) a + dist a (y i) = dist (x i) (y i) ∧
        dist (x i) b + dist b (y i) = dist (x i) (y i)) ∨
      (dist (x i) b + dist b a = dist (x i) a ∧
        dist b a + dist a (y i) = dist b (y i) ∧
        dist (x i) b + dist b (y i) = dist (x i) (y i) ∧
        dist (x i) a + dist a (y i) = dist (x i) (y i)) := by
  refine ⟨fun i => pole i (2 * N), fun i => pole i (-(2 * N)), ?_⟩
  intro a ha b hb
  obtain ⟨i, hi⟩ := exists_coord_dist hd a b
  refine ⟨i, ?_⟩
  rcases le_total (b i) (a i) with h | h
  · exact Or.inl (parallel_bundle_pole i N hN S hS a ha b hb hi h)
  · refine Or.inr (parallel_bundle_pole i N hN S hS b hb a ha ?_ h)
    rw [dist_comm, hi, abs_sub_comm]

end SupMetric
