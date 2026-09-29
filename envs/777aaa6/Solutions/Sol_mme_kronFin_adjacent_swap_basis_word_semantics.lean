-- Prove2me | solution 1 for mme_kronFin_adjacent_swap_basis_word_semantics
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T20:17:16.648744+00:00
-- url     : https://prove2.me/submissions/ce866300-fc68-4c7e-8171-8e0e4791db9b

import Definitions.Def_mme_kronFin_adjacent_swap_data

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.TensorObj

private theorem basis_apply_heq
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) (j : Fin (n + 1)) (i : Fin d)
    {index : Fin (n + 2) → Type u}
    (b : ∀ r, Basis (index r) K ((T r).V i)) (r : Fin (n + 2)) :
    HEq (kronFinAdjacentSwapBasis T j i b r)
      (b (Equiv.swap j.castSucc j.succ r)) := by
  induction n with
  | zero =>
      have hj : j = 0 := Fin.eq_zero j
      subst hj
      refine Fin.cases ?_ (fun r ↦ Fin.cases ?_ (fun s ↦ ?_) r) r
      · change HEq (b 1) (b (Equiv.swap (0 : Fin 2) 1 0))
        rw [Equiv.swap_apply_left]
      · change HEq (b 0) (b (Equiv.swap (0 : Fin 2) 1 1))
        rw [Equiv.swap_apply_right]
      · exact Fin.elim0 s
  | succ n ih =>
      revert T index b r
      refine Fin.cases ?_ (fun q T index b r ↦ ?_) j
      · intro T index b r
        refine Fin.cases ?_ (fun r ↦ Fin.cases ?_ (fun s ↦ ?_) r) r
        · change HEq (b 1)
            (b (Equiv.swap (0 : Fin (n + 3)) 1 0))
          rw [Equiv.swap_apply_left]
        · change HEq (b 0)
            (b (Equiv.swap (0 : Fin (n + 3)) 1 1))
          rw [Equiv.swap_apply_right]
        · change HEq (b s.succ.succ)
            (b (Equiv.swap (0 : Fin (n + 3)) 1 s.succ.succ))
          rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by
            intro h
            have hs : s.succ = 0 := Fin.succ_inj.mp h
            exact Fin.succ_ne_zero s hs)]
      · refine Fin.cases ?_ (fun s ↦ ?_) r
        · change HEq (b 0)
            (b (Equiv.swap q.succ.castSucc q.succ.succ 0))
          rw [Equiv.swap_apply_of_ne_of_ne (by
              intro h
              apply Fin.succ_ne_zero q.castSucc
              simpa only [Fin.castSucc_succ] using h.symm) (by
              intro h
              exact Fin.succ_ne_zero q.succ h.symm)]
        · have hs := ih
            (fun r : Fin (n + 2) ↦ T r.succ) q
            (index := fun r : Fin (n + 2) ↦ index r.succ)
            (fun r : Fin (n + 2) ↦ b r.succ) s
          have hswap :
              (Equiv.swap q.castSucc q.succ s).succ =
                Equiv.swap q.succ.castSucc q.succ.succ s.succ := by
            simpa only [Fin.succ_castSucc] using
              Function.Injective.map_swap
                (Fin.succ_injective _) q.castSucc q.succ s
          rw [← hswap]
          exact hs

private theorem word_apply_heq
    {n : ℕ} {index : Fin (n + 2) → Type u} (j : Fin (n + 1))
    (w : ∀ r, kronFinAdjacentSwapIndex index j r) (r : Fin (n + 2)) :
    HEq (kronFinAdjacentUnswapWord j w r)
      (w (Equiv.swap j.castSucc j.succ r)) := by
  induction n with
  | zero =>
      have hj : j = 0 := Fin.eq_zero j
      subst hj
      refine Fin.cases ?_ (fun r ↦ Fin.cases ?_ (fun s ↦ ?_) r) r
      · change HEq (w 1) (w (Equiv.swap (0 : Fin 2) 1 0))
        rw [Equiv.swap_apply_left]
      · change HEq (w 0) (w (Equiv.swap (0 : Fin 2) 1 1))
        rw [Equiv.swap_apply_right]
      · exact Fin.elim0 s
  | succ n ih =>
      revert w r
      refine Fin.cases ?_ (fun q w r ↦ ?_) j
      · intro w r
        refine Fin.cases ?_ (fun r ↦ Fin.cases ?_ (fun s ↦ ?_) r) r
        · change HEq (w 1)
            (w (Equiv.swap (0 : Fin (n + 3)) 1 0))
          rw [Equiv.swap_apply_left]
        · change HEq (w 0)
            (w (Equiv.swap (0 : Fin (n + 3)) 1 1))
          rw [Equiv.swap_apply_right]
        · change HEq (w s.succ.succ)
            (w (Equiv.swap (0 : Fin (n + 3)) 1 s.succ.succ))
          rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by
            intro h
            have hs : s.succ = 0 := Fin.succ_inj.mp h
            exact Fin.succ_ne_zero s hs)]
      · refine Fin.cases ?_ (fun s ↦ ?_) r
        · change HEq (w 0)
            (w (Equiv.swap q.succ.castSucc q.succ.succ 0))
          rw [Equiv.swap_apply_of_ne_of_ne (by
              intro h
              apply Fin.succ_ne_zero q.castSucc
              simpa only [Fin.castSucc_succ] using h.symm) (by
              intro h
              exact Fin.succ_ne_zero q.succ h.symm)]
        · have hs := ih q
            (index := fun r : Fin (n + 2) ↦ index r.succ)
            (fun r : Fin (n + 2) ↦ w r.succ) s
          have hswap :
              (Equiv.swap q.castSucc q.succ s).succ =
                Equiv.swap q.succ.castSucc q.succ.succ s.succ := by
            simpa only [Fin.succ_castSucc] using
              Function.Injective.map_swap
                (Fin.succ_injective _) q.castSucc q.succ s
          rw [← hswap]
          exact hs

end MME.TensorObj

theorem solution
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) (j : Fin (n + 1)) :
    (∀ (i : Fin d) (index : Fin (n + 2) → Type u)
        (b : ∀ r, Basis (index r) K ((T r).V i)) (r : Fin (n + 2)),
      HEq (TensorObj.kronFinAdjacentSwapBasis T j i b r)
        (b (Equiv.swap j.castSucc j.succ r))) ∧
    ∀ (index : Fin (n + 2) → Type u)
        (w : ∀ r, TensorObj.kronFinAdjacentSwapIndex index j r)
        (r : Fin (n + 2)),
      HEq (TensorObj.kronFinAdjacentUnswapWord j w r)
        (w (Equiv.swap j.castSucc j.succ r)) := by
  exact ⟨fun i index b r ↦ TensorObj.basis_apply_heq T j i b r,
    fun index w r ↦ TensorObj.word_apply_heq j w r⟩
