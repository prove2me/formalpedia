-- Prove2me | solution 1 for Heisenberg125.exists_nonempty_zeroSum_sublist_family
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:46:40.921919+00:00
-- url     : https://prove2.me/submissions/6ae14541-c605-47ac-b32b-d7edcad0607b

-- Sol generated from Algebra/Heisenberg125/ZeroSumTwoDim.lean
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_ZeroSumTwoDim
import Theorems.Thm_Heisenberg125_exists_nonempty_zeroSum_family
/-
# The Davenport constant of `(ZMod p)^2`: `D(C_p ⊕ C_p) ≤ 2p - 1`

This file proves, by an application of the **Chevalley–Warning theorem**, that
any sequence of `2p - 1` vectors in `(ZMod p)^2` admits a nonempty subsequence
summing to zero (`exists_nonempty_zeroSum_sublist`).

This is the additive-combinatorial engine behind the "line bound" of
`Algebra.Heisenberg125.LineBound`: the preimage in `H_{p^3}` of a line through
the origin of `(ZMod p)^2` is an abelian subgroup isomorphic to `C_p ⊕ C_p`, and
product-one-freeness there is exactly zero-sum-freeness in `(ZMod p)^2`.

The Finset version `exists_nonempty_zeroSum_pair` is stated for two coordinate
functions `u, w : Fin n → ZMod p` so that it can be applied directly to
arbitrary pairs of `ZMod p`-valued statistics of a sequence.
-/

open Heisenberg125

open Finset MvPolynomial

variable {p : ℕ} [Fact p.Prime]









open Heisenberg125 in
theorem solution{α : Type*} {k : ℕ} (M : List α)
    (u : Fin k → α → ZMod p) (hM : k * (p - 1) < M.length) :
    ∃ T : List α, T.Sublist M ∧ T ≠ [] ∧ ∀ j, (T.map (u j)).sum = 0 := by
  classical
  obtain ⟨t, htne, ht⟩ :=
    exists_nonempty_zeroSum_family (fun j => fun i : Fin M.length => u j (M.get i))
      (by simpa using hM)
  set idxs : List (Fin M.length) := (List.finRange M.length).filter (fun i => decide (i ∈ t))
    with hidxs
  have hnodup : idxs.Nodup := (List.nodup_finRange _).filter _
  have htoFinset : idxs.toFinset = t := by
    ext i
    simp [hidxs]
  have hsum : ∀ f : α → ZMod p, ((idxs.map M.get).map f).sum = ∑ i ∈ t, f (M.get i) := by
    intro f
    rw [List.map_map, ← htoFinset, List.sum_toFinset _ hnodup]
    rfl
  refine ⟨idxs.map M.get, ?_, ?_, ?_⟩
  · have : (idxs.map M.get).Sublist ((List.finRange M.length).map M.get) :=
      List.Sublist.map _ (by rw [hidxs]; exact List.filter_sublist)
    rwa [List.map_get_finRange] at this
  · obtain ⟨i, hi⟩ := htne
    have hmem : i ∈ idxs := by
      rw [hidxs, List.mem_filter]
      exact ⟨List.mem_finRange i, by simpa using hi⟩
    intro hc
    have hmm : M.get i ∈ idxs.map M.get := List.mem_map_of_mem hmem
    rw [hc] at hmm
    simp at hmm
  · intro j
    rw [hsum]
    exact ht j
