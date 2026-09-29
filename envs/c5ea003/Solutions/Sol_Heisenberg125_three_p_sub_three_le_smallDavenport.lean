-- Prove2me | solution 1 for Heisenberg125.three_p_sub_three_le_smallDavenport
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T20:37:19.846656+00:00
-- url     : https://prove2.me/submissions/a3bbd15c-962c-44b9-83fd-ea78a34c618b

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_LowerBound

open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} [NeZero p] :
    3 * (p - 1) ≤ smallDavenport (Heis p) := by
  classical
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hfree : ProductOneFree (extremalSeq p) := by
    have hab : ∀ L : List (Heis p),
        L.prod.a = (L.map Heis.a).sum ∧ L.prod.b = (L.map Heis.b).sum := by
      intro L
      induction L with
      | nil => exact ⟨rfl, rfl⟩
      | cons g L ih =>
        simp only [List.prod_cons, List.map_cons, List.sum_cons, mul_a, mul_b, ih.1, ih.2]
        exact ⟨trivial, trivial⟩
    have hsmall : ∀ i : ℕ, i < p → (i : ZMod p) = 0 → i = 0 := by
      intro i hi h
      have hd : p ∣ i := (CharP.cast_eq_zero_iff (ZMod p) p i).1 h
      exact Nat.eq_zero_of_dvd_of_lt hd hi
    have hv : ∀ l : ℕ, (List.replicate l (v p)).prod = ⟨0, 0, (l : ZMod p)⟩ := by
      intro l
      induction l with
      | zero =>
        rw [List.replicate_zero, List.prod_nil]
        ext <;> simp
      | succ l ih =>
        rw [List.replicate_succ, List.prod_cons, ih]
        ext <;> simp [v] <;> ring
    intro T hT hne ⟨M, hM, hprod⟩
    unfold extremalSeq at hT
    obtain ⟨T12, T3, rfl, h12, h3⟩ := List.sublist_append_iff.1 hT
    obtain ⟨T1, T2, rfl, h1, h2⟩ := List.sublist_append_iff.1 h12
    obtain ⟨i, hi, rfl⟩ := List.sublist_replicate_iff.1 h1
    obtain ⟨j, hj, rfl⟩ := List.sublist_replicate_iff.1 h2
    obtain ⟨l, hl, rfl⟩ := List.sublist_replicate_iff.1 h3
    have hA : (i : ZMod p) = 0 := by
      have e : ((List.replicate i (x p) ++ List.replicate j (y p) ++ List.replicate l (v p)).map
          Heis.a).sum = (i : ZMod p) := by
        simp [x, y, v]
      rw [← e, ← (hM.map Heis.a).sum_eq, ← (hab M).1, hprod]
      rfl
    have hB : (j : ZMod p) = 0 := by
      have e : ((List.replicate i (x p) ++ List.replicate j (y p) ++ List.replicate l (v p)).map
          Heis.b).sum = (j : ZMod p) := by
        simp [x, y, v]
      rw [← e, ← (hM.map Heis.b).sum_eq, ← (hab M).2, hprod]
      rfl
    have hi0 := hsmall i (by omega) hA
    have hj0 := hsmall j (by omega) hB
    subst hi0
    subst hj0
    simp only [List.replicate_zero, List.nil_append] at hM hne
    have hM2 := List.perm_replicate.1 hM
    rw [hM2, hv] at hprod
    have hc : (l : ZMod p) = 0 := by
      have := congrArg Heis.c hprod
      simpa using this
    have hl0 := hsmall l (by omega) hc
    subst hl0
    exact hne rfl
  -- product-one-free sequences are shorter than the group
  have hbound : ∀ L : List (Heis p), ProductOneFree L → L.length < Fintype.card (Heis p) := by
    intro L hL
    by_contra hge
    rw [not_lt] at hge
    have hcard : Fintype.card (Heis p) < Fintype.card (Fin (L.length + 1)) := by
      rw [Fintype.card_fin]
      omega
    obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun m : Fin (L.length + 1) => (L.take m).prod) hcard
    wlog hlt : (i : ℕ) < j generalizing i j
    · exact this j i hij.symm heq.symm (lt_of_le_of_ne (not_lt.1 hlt) (fun h => hij (Fin.ext h.symm)))
    have hsplit : L.take j = L.take i ++ (L.drop i).take (j - i) := by
      rw [← List.take_add]
      congr 1
      omega
    rw [hsplit, List.prod_append] at heq
    have hT1 : ((L.drop i).take (j - i)).prod = 1 := by
      have := congrArg (fun g => ((L.take i).prod)⁻¹ * g) heq
      simpa using this.symm
    apply hL ((L.drop i).take (j - i))
      ((List.take_sublist _ _).trans (List.drop_sublist _ _))
    · intro h
      have hlen := congrArg List.length h
      simp only [List.length_take, List.length_drop, List.length_nil] at hlen
      have hj := j.isLt
      omega
    · exact ⟨_, List.Perm.refl _, hT1⟩
  have hbdd : BddAbove (productOneFreeLengths (Heis p)) := by
    refine ⟨Fintype.card (Heis p), fun n hn => ?_⟩
    obtain ⟨L, hlen, hL⟩ := hn
    rw [← hlen]
    exact (hbound L hL).le
  have hmem : 3 * (p - 1) ∈ productOneFreeLengths (Heis p) := by
    refine ⟨extremalSeq p, ?_, hfree⟩
    simp [extremalSeq]
    omega
  exact le_csSup hbdd hmem
