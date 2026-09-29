-- Prove2me | solution 1 for TropicalLA.IsTropEigenBot.exists_critical_suppCycle
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T10:10:01.113712+00:00
-- url     : https://prove2.me/submissions/7ea37439-24bf-44ce-8eb2-3f0535311f54

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι (WithBot ℝ)} {lam : ℝ}
    {v : ι → ℝ} (h : IsTropEigenBot A lam v) :
    ∃ (m : ℕ) (c : ℕ → ι), 0 < m ∧ c m = c 0 ∧ IsSuppWalk A c m ∧
      pathWeight (finPart A) c m = m * lam := by
  classical
  have hcoe : ∀ x : WithBot ℝ, x ≠ ⊥ → x = ((x.unbotD 0 : ℝ) : WithBot ℝ) := by
    intro x hx
    induction x using WithBot.recBotCoe with
    | bot => exact absurd rfl hx
    | coe a => simp
  have hedge : ∀ i j, A i j ≠ ⊥ → finPart A i j + v j ≤ lam + v i := by
    intro i j hne
    have h1 : A i j + (v j : WithBot ℝ) ≤ univ.sup (fun j => A i j + (v j : WithBot ℝ)) :=
      Finset.le_sup (f := fun j => A i j + (v j : WithBot ℝ)) (mem_univ j)
    have h2 : univ.sup (fun j => A i j + (v j : WithBot ℝ)) = ((lam + v i : ℝ) : WithBot ℝ) := h i
    have h3 : A i j = ((finPart A i j : ℝ) : WithBot ℝ) := hcoe _ hne
    rw [h2, h3, ← WithBot.coe_add, WithBot.coe_le_coe] at h1
    exact h1
  have htight : ∀ i, ∃ j, A i j ≠ ⊥ ∧ finPart A i j + v j = lam + v i := by
    intro i
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup (univ : Finset ι) univ_nonempty
      (fun j => A i j + (v j : WithBot ℝ))
    have hi : univ.sup (fun j => A i j + (v j : WithBot ℝ)) = ((lam + v i : ℝ) : WithBot ℝ) := h i
    rw [hi] at hj
    have hne : A i j ≠ ⊥ := by
      intro hbot
      rw [hbot, WithBot.bot_add] at hj
      exact WithBot.coe_ne_bot hj
    refine ⟨j, hne, ?_⟩
    have h2 : A i j = ((finPart A i j : ℝ) : WithBot ℝ) := hcoe _ hne
    rw [h2, ← WithBot.coe_add, WithBot.coe_inj] at hj
    linarith
  -- a tight closed support walk
  have hcrit : ∃ (m : ℕ) (c : ℕ → ι), 0 < m ∧ c m = c 0 ∧ IsSuppWalk A c m ∧
      pathWeight (finPart A) c m = m * lam := by
    choose f hfs hf using htight
    obtain ⟨i0⟩ := ‹Nonempty ι›
    have key : ∀ a b : ℕ, a < b → f^[a] i0 = f^[b] i0 → ∃ (m : ℕ) (c : ℕ → ι), 0 < m ∧
        c m = c 0 ∧ IsSuppWalk A c m ∧ pathWeight (finPart A) c m = m * lam := by
      intro a b hab hfab
      set p : ℕ → ι := fun s => f^[a + s] i0 with hp
      have hpsucc : ∀ s, p (s + 1) = f (p s) := by
        intro s
        show f^[a + (s + 1)] i0 = f (f^[a + s] i0)
        rw [show a + (s + 1) = (a + s) + 1 by omega]
        exact Function.iterate_succ_apply' f (a + s) i0
      have htel : ∀ n, pathWeight (finPart A) p n + v (p n) = n * lam + v (p 0) := by
        intro n
        induction n with
        | zero => simp [pathWeight]
        | succ n ih =>
          have e : pathWeight (finPart A) p (n + 1)
              = pathWeight (finPart A) p n + finPart A (p n) (p (n + 1)) := by
            unfold pathWeight
            rw [Finset.sum_range_succ]
          rw [e, hpsucc n]
          have := hf (p n)
          push_cast
          linarith
      have hclosed : p (b - a) = p 0 := by
        show f^[a + (b - a)] i0 = f^[a + 0] i0
        rw [show a + (b - a) = b by omega]
        exact hfab.symm
      refine ⟨b - a, p, by omega, hclosed, ?_, ?_⟩
      · intro t _
        rw [hpsucc t]
        exact hfs (p t)
      · have h2 := htel (b - a)
        rw [hclosed] at h2
        linarith
    obtain ⟨x, y, hxy, hfxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun s : Fin (Fintype.card ι + 1) => f^[s] i0) (by simp)
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with hlt | hlt
    · exact key x y hlt hfxy
    · exact key y x hlt hfxy.symm
  exact hcrit
