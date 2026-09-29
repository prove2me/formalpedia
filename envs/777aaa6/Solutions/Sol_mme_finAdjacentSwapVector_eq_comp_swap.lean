-- Prove2me | solution 1 for mme_finAdjacentSwapVector_eq_comp_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T20:16:33.978567+00:00
-- url     : https://prove2.me/submissions/d798b867-ba0c-45c0-9c87-a250b802af89

import Definitions.Def_mme_kronFin_adjacent_swap_data

open MME Module MME.TensorObj

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {α : Sort u} {n : ℕ} (T : Fin (n + 2) → α) (j : Fin (n + 1)) :
    finAdjacentSwapVector T j =
      fun r ↦ T (Equiv.swap j.castSucc j.succ r) := by
  induction n with
  | zero =>
      have hj : j = 0 := Fin.eq_zero j
      subst hj
      funext r
      refine Fin.cases ?_ (fun r ↦ Fin.cases ?_ (fun s ↦ ?_) r) r
      · change T 1 = T (Equiv.swap (0 : Fin 2) 1 0)
        simp only [Equiv.swap_apply_left]
      · change T 0 = T (Equiv.swap (0 : Fin 2) 1 1)
        simp only [Equiv.swap_apply_right]
      · exact Fin.elim0 s
  | succ n ih =>
      revert T
      refine Fin.cases ?_ (fun q T ↦ ?_) j
      · intro T
        funext r
        refine Fin.cases ?_ (fun r ↦ Fin.cases ?_ (fun s ↦ ?_) r) r
        · change T 1 = T (Equiv.swap (0 : Fin (n + 3)) 1 0)
          simp only [Equiv.swap_apply_left]
        · change T 0 = T (Equiv.swap (0 : Fin (n + 3)) 1 1)
          simp only [Equiv.swap_apply_right]
        · change T s.succ.succ =
            T (Equiv.swap (0 : Fin (n + 3)) 1 s.succ.succ)
          exact congrArg T
            (Equiv.swap_apply_of_ne_of_ne (by simp) (by
              intro h
              have hs : s.succ = 0 := Fin.succ_inj.mp h
              exact Fin.succ_ne_zero s hs)).symm
      · funext r
        refine Fin.cases ?_ (fun s ↦ ?_) r
        · change T 0 =
            T (Equiv.swap q.succ.castSucc q.succ.succ 0)
          exact congrArg T
            (Equiv.swap_apply_of_ne_of_ne (by
              intro h
              apply Fin.succ_ne_zero q.castSucc
              simpa only [Fin.castSucc_succ] using h.symm) (by
              intro h
              exact Fin.succ_ne_zero q.succ h.symm)).symm
        · change finAdjacentSwapVector
              (fun r : Fin (n + 2) ↦ T r.succ) q s =
            T (Equiv.swap q.succ.castSucc q.succ.succ s.succ)
          rw [congrFun (ih (fun r : Fin (n + 2) ↦ T r.succ) q) s]
          exact congrArg T (by
            simpa only [Fin.succ_castSucc] using
              Function.Injective.map_swap
                (Fin.succ_injective _) q.castSucc q.succ s)
