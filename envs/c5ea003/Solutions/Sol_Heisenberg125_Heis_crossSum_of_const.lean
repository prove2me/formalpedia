-- Prove2me | solution 1 for Heisenberg125.Heis.crossSum_of_const
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T03:42:07.201557+00:00
-- url     : https://prove2.me/submissions/6c3b3a45-cd5b-4f9a-8acc-84a008a2a789

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} {L : List (Heis p)} {α β : ZMod p}
    (h : ∀ g ∈ L, g.a = α ∧ g.b = β) :
    crossSum L = α * β * (L.length.choose 2 : ℕ) := by
  -- the `b`-sum of a list with constant `b = β` is `length · β`
  have hbsum : ∀ M : List (Heis p), (∀ x ∈ M, x.b = β) → bsum M = (M.length : ZMod p) * β := by
    intro M hM
    induction M with
    | nil => simp [bsum]
    | cons x M ihx =>
      have hrest := ihx (fun y hy => hM y (List.mem_cons_of_mem x hy))
      simp only [bsum, List.map_cons, List.sum_cons] at hrest ⊢
      rw [hrest, hM x List.mem_cons_self, List.length_cons]
      push_cast
      ring
  induction L with
  | nil => simp [crossSum]
  | cons g L ih =>
    have hg := h g List.mem_cons_self
    have hL : ∀ x ∈ L, x.a = α ∧ x.b = β := fun x hx => h x (List.mem_cons_of_mem g hx)
    -- `C(n+1, 2) = C(n, 2) + n`
    rw [crossSum, ih hL, hbsum L (fun x hx => (hL x hx).2), hg.1, List.length_cons,
      Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    ring
