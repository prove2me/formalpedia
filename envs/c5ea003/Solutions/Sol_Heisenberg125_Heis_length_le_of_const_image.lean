-- Prove2me | solution 1 for Heisenberg125.Heis.length_le_of_const_image
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T06:19:02.936401+00:00
-- url     : https://prove2.me/submissions/6fcad75c-f417-4420-a950-0124bb9f254b

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_CosetBound
import Definitions.Def_Algebra_Heisenberg125_LowerBound

open Heisenberg125 Heis Finset in
theorem solution {p : ℕ} (hodd : Odd p) {C : List (Heis p)} {α β : ZMod p}
    (hfree : ProductOneFree C) (hconst : ∀ g ∈ C, g.a = α ∧ g.b = β) :
    C.length ≤ 2 * p - 2 := by
  classical
  -- a product of elements sharing `(a, b) = (α, β)`, in any order
  have hprod : ∀ L : List (Heis p), (∀ g ∈ L, g.a = α ∧ g.b = β) →
      L.prod = ⟨(L.length : ZMod p) * α, (L.length : ZMod p) * β,
        (L.map Heis.c).sum + α * β * ((L.length.choose 2 : ℕ) : ZMod p)⟩ := by
    intro L
    induction L with
    | nil =>
      intro _
      ext <;> simp
    | cons g L ih =>
      intro hL
      obtain ⟨hga, hgb⟩ := hL g (List.mem_cons_self ..)
      rw [List.prod_cons, ih (fun x hx => hL x (List.mem_cons_of_mem g hx))]
      ext
      · simp only [mul_a, List.length_cons, hga]
        push_cast
        ring
      · simp only [mul_b, List.length_cons, hgb]
        push_cast
        ring
      · simp only [mul_c, List.length_cons, List.map_cons, List.sum_cons, hga,
          Nat.choose_succ_succ, Nat.choose_one_right]
        push_cast
        ring
  by_contra hlen
  have hlen' : 2 * p - 1 ≤ C.length := by omega
  -- Erdős–Ginzburg–Ziv: `p` of the central coordinates sum to zero
  obtain ⟨t, -, htcard, htsum⟩ := ZMod.erdos_ginzburg_ziv
    (fun i : Fin C.length => (C.get i).c) (s := univ)
    (by rw [card_univ, Fintype.card_fin]; exact hlen')
  set idx := (List.finRange C.length).filter (fun i => i ∈ t) with hidx
  set T := idx.map C.get with hT
  have hsub : T.Sublist C := by
    have h1 : (List.finRange C.length).map C.get = C := by
      rw [← List.ofFn_eq_map, List.ofFn_get]
    conv_rhs => rw [← h1]
    exact (List.filter_sublist).map _
  have hnodup : idx.Nodup := (List.nodup_finRange _).filter _
  have htoF : idx.toFinset = t := by
    ext i
    simp [hidx, List.mem_filter, List.mem_finRange]
  have hTlen : T.length = p := by
    rw [hT, List.length_map, ← List.toFinset_card_of_nodup hnodup, htoF, htcard]
  have hp1 : 1 ≤ p := hodd.pos
  have hne : T ≠ [] := by
    intro h
    rw [h] at hTlen
    simp at hTlen
    omega
  have hTconst : ∀ g ∈ T, g.a = α ∧ g.b = β := fun g hg => hconst g (hsub.subset hg)
  have hsumc : (T.map Heis.c).sum = 0 := by
    rw [hT, List.map_map, ← List.sum_toFinset _ hnodup, htoF]
    exact htsum
  obtain ⟨k, hk⟩ := hodd
  have hc2 : p.choose 2 = p * k := by
    rw [Nat.choose_two_right, show p - 1 = 2 * k by omega,
      show p * (2 * k) = 2 * (p * k) by ring, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hTprod : T.prod = 1 := by
    rw [hprod T hTconst, hTlen, hsumc, hc2]
    push_cast
    rw [ZMod.natCast_self]
    ext <;> simp
  exact hfree T hsub hne ⟨T, List.Perm.refl T, hTprod⟩
