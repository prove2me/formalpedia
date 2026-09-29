-- Prove2me | solution 1 for MarkovMixing.random_map_representation
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T18:29:04.722202+00:00
-- url     : https://prove2.me/submissions/f43256ce-4adf-4e1f-a614-cacac11b8145

import Definitions.Def_mm_cftp

/-!
# Every finite chain has a random mapping representation

Take the update maps to have **independent coordinates**: let
`ν(f) = ∏_x P(x, f(x))`, i.e. draw `f(x)` from the row `P(x,·)`
independently for each state `x`.  Expanding the product of the row sums
shows `ν` is a probability distribution on `V → V`, and conditioning on the
value at a single coordinate leaves the other rows summing to `1`, so
`ν{f : f(x) = y} = P(x,y)`.
-/

namespace MarkovMixing

open scoped BigOperators

end MarkovMixing

open MarkovMixing

/-- **LPW §1.2**: every stochastic matrix on a finite state space admits a
random mapping representation. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) :
    ∃ ν : (V → V) → ℝ, IsRandomMapRep P ν := by
  classical
  refine ⟨fun f => ∏ x : V, P x (f x),
    ⟨⟨fun f => Finset.prod_nonneg fun x _ => hP.1 x (f x), ?_⟩, ?_⟩⟩
  · have h := Finset.prod_univ_sum (fun _ : V => (Finset.univ : Finset V))
      (fun (x : V) (y : V) => P x y)
    simp only [Fintype.piFinset_univ, hP.2, Finset.prod_const_one] at h
    exact h.symm
  · intro x₀ y₀
    set g : V → V → ℝ :=
      fun x y => if x = x₀ then (if y = y₀ then P x₀ y₀ else 0) else P x y with hg
    have hterm : ∀ f : V → V,
        (if f x₀ = y₀ then ∏ x : V, P x (f x) else 0) = ∏ x : V, g x (f x) := by
      intro f
      have hsplit1 : ∏ x : V, g x (f x)
          = g x₀ (f x₀) * ∏ x ∈ Finset.univ.erase x₀, g x (f x) :=
        (Finset.mul_prod_erase Finset.univ (fun x => g x (f x)) (Finset.mem_univ x₀)).symm
      have hsplit2 : ∏ x : V, P x (f x)
          = P x₀ (f x₀) * ∏ x ∈ Finset.univ.erase x₀, P x (f x) :=
        (Finset.mul_prod_erase Finset.univ (fun x => P x (f x)) (Finset.mem_univ x₀)).symm
      have herase : ∏ x ∈ Finset.univ.erase x₀, g x (f x)
          = ∏ x ∈ Finset.univ.erase x₀, P x (f x) := by
        refine Finset.prod_congr rfl fun x hx => ?_
        have hne : x ≠ x₀ := Finset.ne_of_mem_erase hx
        simp [hg, hne]
      rw [hsplit1, herase]
      by_cases h : f x₀ = y₀
      · rw [if_pos h, hsplit2]
        congr 1
        simp [hg, h]
      · rw [if_neg h]
        have hz : g x₀ (f x₀) = 0 := by simp [hg, h]
        rw [hz, zero_mul]
    rw [Finset.sum_filter]
    simp only [hterm]
    have h := Finset.prod_univ_sum (fun _ : V => (Finset.univ : Finset V)) g
    simp only [Fintype.piFinset_univ] at h
    rw [← h, Finset.prod_eq_single x₀]
    · simp [hg]
    · intro b _ hb
      simp only [hg]
      simp only [hb, if_false]
      exact hP.2 b
    · intro hcon
      exact absurd (Finset.mem_univ x₀) hcon
