-- Prove2me | solution 1 for SphericalGeometry.shift_mul_order_eq_two_pi_mul_int
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T11:40:58.772506+00:00
-- url     : https://prove2.me/submissions/3aa655ac-a802-4d22-907e-d2dc1a4c2441

import Definitions.Def_spherical_great_circle

open SphericalGeometry

universe u

theorem solution {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : E → E) (v1 v2 : E) (h1 : ‖v1‖ = 1) (h12 : inner ℝ v1 v2 = (0:ℝ))
    (T : ℝ) (k : ℕ)
    (hord : ∀ x : E, w^[k] x = x)
    (heq : ∀ s : ℝ, greatCirclePath v1 v2 (s + T) = w (greatCirclePath v1 v2 s)) :
    ∃ m : ℤ, (k : ℝ) * T = 2 * Real.pi * m := by
  -- iterate the equivariance
  have hiter : ∀ n : ℕ, ∀ s : ℝ,
      greatCirclePath v1 v2 (s + n * T) = w^[n] (greatCirclePath v1 v2 s) := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
        intro s
        have hs : s + ((n : ℝ) + 1) * T = (s + n * T) + T := by ring
        rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring, hs, heq, ih s,
          Function.iterate_succ_apply']
  -- after `k` steps the path returns
  have hper : greatCirclePath v1 v2 ((k : ℝ) * T) = v1 := by
    have h := hiter k 0
    rw [zero_add, hord] at h
    have hg0 : greatCirclePath v1 v2 (0:ℝ) = v1 := by simp [greatCirclePath]
    rw [hg0] at h
    exact h
  -- read off the cosine
  have hs1 : inner ℝ v1 v1 = (1:ℝ) := by
    rw [real_inner_self_eq_norm_sq, h1]; norm_num
  have h21 : inner ℝ v2 v1 = (0:ℝ) := by rw [real_inner_comm]; exact h12
  have hcos : Real.cos ((k : ℝ) * T) = 1 := by
    have := congrArg (fun y => (inner ℝ y v1 : ℝ)) hper
    simp only [greatCirclePath, inner_add_left, real_inner_smul_left, hs1, h21] at this
    linarith [this]
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff ((k : ℝ) * T)).1 hcos
  exact ⟨m, by rw [← hm]; ring⟩
