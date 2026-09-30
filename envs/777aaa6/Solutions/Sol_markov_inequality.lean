-- Prove2me | solution 1 for markov_inequality
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:16:36.187087+00:00
-- url     : https://prove2.me/submissions/6d50a8d0-9712-4c5f-b64e-f0769d1835b2

import Mathlib
import Theorems.Thm_markov_unit

theorem solution (f : ℝ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hf : ∀ x, |x| ≤ 1 → |f x| ≤ 1)
    (hpoly : ∃ p : Polynomial ℝ, p.natDegree = n ∧ ∀ x, p.eval x = f x) :
    ∀ x : ℝ, |x| ≤ 1 → |deriv f x| ≤ n ^ 2 := by
  obtain ⟨p, hdeg, hpf⟩ := hpoly
  have hfp : f = fun x => p.eval x := by
    funext x
    exact (hpf x).symm
  subst hfp
  intro x hx
  rw [Polynomial.deriv]
  exact markov_unit p hdeg.le (fun y hy1 hy2 => hf y (abs_le.mpr ⟨hy1, hy2⟩)) x
    (abs_le.mp hx).1 (abs_le.mp hx).2
