-- Prove2me | solution 2 for DiophantineLattice.rank_one_multiplicity_even_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:50:37.065633+00:00
-- url     : https://prove2.me/submissions/f674f741-c2f6-4534-8647-256e4557c70e

import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Definitions.Def_Novelty_DiophantineLatticeExactOrder
open DiophantineLattice Finset in
theorem solution (t : Fin 1 → ℚ) :
    (∀ (c : ℚ) (S : Finset (Fin 1 → ℤ)),
        (∀ m : Fin 1 → ℤ, m ∈ S ↔ form (1 : Matrix (Fin 1) (Fin 1) ℚ)
          (fun i => t i - emb m i) = c) → Even S.card)
      ↔ ((∃ v : Fin 1 → ℤ, ∀ i, (2 : ℚ) * t i = (v i : ℚ)) ∧ ∀ k : Fin 1 → ℤ, t ≠ emb k) := by
  have hone : ∀ x : Fin 1 → ℚ, form (1 : Matrix (Fin 1) (Fin 1) ℚ) x = x 0 ^ 2 := by
    intro x
    simp [form, bil, Matrix.one_apply, Fin.sum_univ_one]
    ring
  constructor
  · intro heven
    refine ⟨?_, ?_⟩
    · by_contra hno
      have h2 : ∀ m : Fin 1 → ℤ, (2 : ℚ) * t 0 ≠ (m 0 : ℚ) := by
        intro m hm
        exact hno ⟨m, fun i => by
          have hi : i = 0 := Subsingleton.elim i 0
          subst hi
          exact hm⟩
      have hmem : ∀ m : Fin 1 → ℤ, m ∈ ({0} : Finset (Fin 1 → ℤ)) ↔
          form (1 : Matrix (Fin 1) (Fin 1) ℚ) (fun i => t i - emb m i) = t 0 ^ 2 := by
        intro m
        rw [Finset.mem_singleton, hone]
        simp only [emb]
        constructor
        · intro h
          rw [h]
          simp
        · intro h
          have hm : (m 0 : ℚ) * ((m 0 : ℚ) - 2 * t 0) = 0 := by nlinarith [h]
          rcases mul_eq_zero.mp hm with h0 | h0
          · funext i
            have hi : i = 0 := Subsingleton.elim i 0
            subst hi
            exact_mod_cast h0
          · exact absurd (by linarith [h0] : (2 : ℚ) * t 0 = (m 0 : ℚ)) (h2 m)
      have hev := heven _ _ hmem
      simp at hev
    · intro k hk
      have hmem : ∀ m : Fin 1 → ℤ, m ∈ ({k} : Finset (Fin 1 → ℤ)) ↔
          form (1 : Matrix (Fin 1) (Fin 1) ℚ) (fun i => t i - emb m i) = 0 := by
        intro m
        rw [Finset.mem_singleton, hone, hk]
        simp only [emb]
        constructor
        · intro h
          rw [h]
          simp
        · intro h
          have hm : ((k 0 : ℚ) - (m 0 : ℚ)) = 0 := by
            have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
            exact this
          funext i
          have hi : i = 0 := Subsingleton.elim i 0
          subst hi
          have hmk : (m 0 : ℚ) = (k 0 : ℚ) := by linarith
          exact_mod_cast hmk
      have hev := heven 0 {k} hmem
      simp at hev
  · rintro ⟨⟨v, hv⟩, hnotlat⟩ c S hS
    have hvodd : ∀ m : Fin 1 → ℤ, v 0 ≠ 2 * m 0 := by
      intro m hm
      refine hnotlat m ?_
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      have h0 := hv 0
      simp only [emb]
      have : (v 0 : ℚ) = 2 * (m 0 : ℚ) := by exact_mod_cast hm
      linarith
    have hform : ∀ m : Fin 1 → ℤ, form (1 : Matrix (Fin 1) (Fin 1) ℚ)
        (fun i => t i - emb (fun j => v j - m j) i)
          = form (1 : Matrix (Fin 1) (Fin 1) ℚ) (fun i => t i - emb m i) := by
      intro m
      rw [hone, hone]
      have hv0 : ((v 0 : ℤ) : ℚ) = 2 * t 0 := (hv 0).symm
      simp only [emb]
      push_cast
      rw [hv0]
      ring
    have hmem : ∀ m ∈ S, (fun j => v j - m j) ∈ S := by
      intro m hm
      rw [hS] at hm ⊢
      rw [hform m]
      exact hm
    have hnefix : ∀ m ∈ S, (fun j => v j - m j) ≠ m := by
      intro m _ h0
      have hj := congrFun h0 0
      exact hvodd m (by omega)
    have hinv : ∀ (m : Fin 1 → ℤ), m ∈ S → (fun j => v j - (fun j => v j - m j) j) = m := by
      intro m _
      funext j
      simp
    have hsum : ∑ _x ∈ S, (1 : ZMod 2) = 0 :=
      Finset.sum_involution (fun m _ => fun j => v j - m j) (fun m _ => by decide)
        (fun m hm _ => hnefix m hm) (fun m hm => hmem m hm) (fun m hm => hinv m hm)
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
    exact ZMod.natCast_eq_zero_iff_even.mp hsum
