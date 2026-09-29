-- Prove2me | solution 1 for Heisenberg125.Heis.productOneFree_extremalSeq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T20:24:00.504635+00:00
-- url     : https://prove2.me/submissions/775ead61-0512-402b-be60-20bde50a71ea

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_LowerBound

open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} (hp : 0 < p) : ProductOneFree (extremalSeq p) := by
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
