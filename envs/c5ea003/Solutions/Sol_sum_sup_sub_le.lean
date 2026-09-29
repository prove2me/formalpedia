-- Prove2me | solution 1 for sum_sup_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-24T01:45:06.048584+00:00
-- url     : https://prove2.me/submissions/b1df8078-2d59-4555-97cf-e5f8876bd835

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

open Finset

theorem solution
    {ι S : Type*} [DecidableEq ι] [Fintype ι] [Fintype S] [Nonempty S]
    (X : ι → S → ℝ) (hX : ∀ i s, 0 ≤ X i s)
    (Z : ℝ) (Zk : ι → ℝ)
    (hZ : Z = Finset.univ.sup' Finset.univ_nonempty (fun s => ∑ i, X i s))
    (hZk : ∀ k, Zk k = Finset.univ.sup' Finset.univ_nonempty (fun s => ∑ i ∈ Finset.univ.erase k, X i s)) :
    ∑ k, (Z - Zk k) ≤ Z := by
  obtain ⟨sstar, -, hsstar⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset S)) Finset.univ_nonempty
      (fun s => ∑ i, X i s)
  have hZval : Z = ∑ i, X i sstar := by rw [hZ, hsstar]
  have hlb : ∀ k, Z - X k sstar ≤ Zk k := by
    intro k
    have hmem : ∑ i ∈ univ.erase k, X i sstar
        ≤ Finset.univ.sup' Finset.univ_nonempty (fun s => ∑ i ∈ univ.erase k, X i s) :=
      Finset.le_sup' (fun s => ∑ i ∈ univ.erase k, X i s) (Finset.mem_univ sstar)
    rw [hZk k]
    have hsplit : ∑ i, X i sstar = X k sstar + ∑ i ∈ univ.erase k, X i sstar :=
      (Finset.add_sum_erase Finset.univ (fun i => X i sstar) (Finset.mem_univ k)).symm
    have : Z - X k sstar = ∑ i ∈ univ.erase k, X i sstar := by
      rw [hZval, hsplit]; ring
    rw [this]; exact hmem
  have hub : ∀ k, Z - Zk k ≤ X k sstar := by
    intro k; linarith [hlb k]
  calc ∑ k, (Z - Zk k) ≤ ∑ k, X k sstar := Finset.sum_le_sum (fun k _ => hub k)
    _ = Z := by rw [hZval]
