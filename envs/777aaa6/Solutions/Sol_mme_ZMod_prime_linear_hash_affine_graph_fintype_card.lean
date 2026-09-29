-- Prove2me | solution 1 for mme_ZMod_prime_linear_hash_affine_graph_fintype_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:52:46.6829+00:00
-- url     : https://prove2.me/submissions/4c2d3a2d-cad5-4fb2-a775-2d23826388e7

import Mathlib
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_finset_card

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p n : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (hcard : Fintype.card I = n + 1)
    (c : I → ZMod p) (j : I) (hc : c j ≠ 0)
    (S : Finset (ZMod p))
    (offset : (I → ZMod p) → ZMod p) :
    ((Finset.univ.filter
      (fun q : (I → ZMod p) × ZMod p ↦
        (∑ i, c i * q.1 i) ∈ S ∧ q.2 = offset q.1)).card) =
      S.card * p ^ n := by
  classical
  let e : I ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hcard
  let we : (I → ZMod p) ≃ (Fin (n + 1) → ZMod p) :=
    Equiv.piCongrLeft (fun _ : Fin (n + 1) ↦ ZMod p) e
  let qe : ((I → ZMod p) × ZMod p) ≃
      ((Fin (n + 1) → ZMod p) × ZMod p) :=
    Equiv.prodCongr we (Equiv.refl (ZMod p))
  let c' : Fin (n + 1) → ZMod p := fun k ↦ c (e.symm k)
  let offset' : (Fin (n + 1) → ZMod p) → ZMod p :=
    fun w ↦ offset (we.symm w)
  have hc' : c' (e j) ≠ 0 := by
    simpa [c'] using hc
  have hsum (w : I → ZMod p) :
      (∑ i, c i * w i) = ∑ k, c' k * (we w) k := by
    apply Fintype.sum_equiv e
    intro i
    simp [c', we]
  let P : ((I → ZMod p) × ZMod p) → Prop := fun q ↦
    (∑ i, c i * q.1 i) ∈ S ∧ q.2 = offset q.1
  let P' : ((Fin (n + 1) → ZMod p) × ZMod p) → Prop := fun q ↦
    (∑ k, c' k * q.1 k) ∈ S ∧ q.2 = offset' q.1
  have hpred (q : (I → ZMod p) × ZMod p) : P q ↔ P' (qe q) := by
    simp only [P, P', qe, Equiv.prodCongr_apply]
    rw [hsum q.1]
    simp [offset', we]
  calc
    ((Finset.univ.filter
      (fun q : (I → ZMod p) × ZMod p ↦
        (∑ i, c i * q.1 i) ∈ S ∧ q.2 = offset q.1)).card) =
        Fintype.card {q // P q} := by
          symm
          simpa only [P] using Fintype.card_subtype P
    _ = Fintype.card {q // P' q} :=
      Fintype.card_congr (qe.subtypeEquiv hpred)
    _ = ((Finset.univ.filter P').card) := Fintype.card_subtype P'
    _ = S.card * p ^ n := by
      simpa [P'] using
        (mme_ZMod_prime_linear_hash_affine_graph_finset_card
          c' (e j) hc' S offset')
