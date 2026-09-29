-- Prove2me | solution 1 for mme_prescribed_histogram_polynomial_type_cover
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T17:27:16.850726+00:00
-- url     : https://prove2.me/submissions/4562a591-625b-4454-bae4-7bf11978deac

import Definitions.Def_mme_recursive_yz_compatibility
import Mathlib

open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem solution {P C W : Type*} [Fintype P] [Fintype C] [Fintype W]
    (cell : P → C) (supported : (Fin 3 → P → W) → Prop)
    (allowed : Fin 3 → (P → W) → Prop)
    (good : Fin 3 → (C → W → ℕ) → Prop) :
    ∃ (types : ℕ) (mu : Fin types → Fin 3 → C → W → ℕ),
      types ≤ (Fintype.card P + 1) ^ (3 * Fintype.card C * Fintype.card W) ∧
      (∀ j, ∃ x, supported x ∧ ∀ i,
        allowed i (x i) ∧ good i (mu j i) ∧ Useful cell (mu j i) (x i)) ∧
      (∀ j i f, allowed i f ∧ Useful cell (mu j i) f →
        allowed i f ∧ good i (count cell f)) ∧
      (∀ x, supported x → (∀ i, allowed i (x i) ∧ good i (count cell (x i))) →
        ∃! j, ∀ i, allowed i (x i) ∧ Useful cell (mu j i) (x i)) := by
  classical
  let H := Fin 3 → C → W → Fin (Fintype.card P + 1)
  have hcount (f : P → W) c w : count cell f c w < Fintype.card P + 1 := by
    have := Finset.card_filter_le (s := Finset.univ) (p := fun p ↦ cell p = c ∧ f p = w)
    simpa only [count, Finset.card_univ, Nat.lt_add_one_iff] using this
  let encode (x : Fin 3 → P → W) : H := fun i c w ↦ ⟨count cell (x i) c w,hcount _ _ _⟩
  let eligible : Finset H := Finset.univ.filter fun h ↦
    ∃ x, supported x ∧ (∀ i, allowed i (x i) ∧ good i (count cell (x i))) ∧ encode x = h
  let J := {h : H // h ∈ eligible}
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let mu (j : Fin (Fintype.card J)) i c w : ℕ := ((e j).val i c w).val
  have hreconstruct (j : Fin (Fintype.card J)) x :
      encode x = (e j).val ↔ ∀ i, Useful cell (mu j i) (x i) := by
    constructor
    · intro hx i c w
      exact congrArg (fun h : H ↦ (h i c w).val) hx
    · intro hx
      funext i c w
      apply Fin.ext
      exact hx i c w
  have hwitness j : ∃ x, supported x ∧ ∀ i,
      allowed i (x i) ∧ good i (mu j i) ∧ Useful cell (mu j i) (x i) := by
    have he := (Finset.mem_filter.mp (e j).property).2
    obtain ⟨x,hs,hx,he⟩ := he
    have hu := (hreconstruct j x).mp he
    refine ⟨x,hs,fun i ↦ ⟨(hx i).1,?_,hu i⟩⟩
    have hh : count cell (x i) = mu j i := funext fun c ↦ funext fun w ↦ hu i c w
    simpa only [hh] using (hx i).2
  refine ⟨Fintype.card J,mu,?_,hwitness,?_,?_⟩
  · have hcard : Fintype.card J ≤ Fintype.card H := Fintype.card_subtype_le _
    convert hcard using 1
    simp only [H,Fintype.card_fun,Fintype.card_fin]
    ring
  · intro j i f hf
    obtain ⟨x,hs,hx⟩ := hwitness j
    have hh : count cell f = mu j i := funext fun c ↦ funext fun w ↦ hf.2 c w
    exact ⟨hf.1,hh ▸ (hx i).2.1⟩
  · intro x hs hx
    have hm : encode x ∈ eligible := Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hs,hx,rfl⟩
    let j := e.symm ⟨encode x,hm⟩
    have hj : encode x = (e j).val := by simp [j]
    refine ⟨j,fun i ↦ ⟨(hx i).1,(hreconstruct j x).mp hj i⟩,?_⟩
    intro k hk
    apply e.injective
    apply Subtype.ext
    exact ((hreconstruct k x).mpr (fun i ↦ (hk i).2)).symm.trans hj
