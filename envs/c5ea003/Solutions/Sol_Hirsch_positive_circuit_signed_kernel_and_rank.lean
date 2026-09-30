-- Prove2me | solution 1 for Hirsch.positive_circuit_signed_kernel_and_rank
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-13T21:13:35.675636+00:00
-- url     : https://prove2.me/submissions/f60b3d5d-7617-4b01-a11d-121b24d9ff42

import Mathlib

open scoped BigOperators

namespace Hirsch.PositiveCircuitRank

/-- Support minimality among nonnegative null vectors controls every SIGNED
null vector on the same support. No full-rank assumption is used. -/
theorem signed_ray_of_minimal (n k : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hAx : A x = 0) (hxne : x ≠ 0)
    (hmin : ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → A y = 0 → y ≠ 0 →
      Function.support y ⊆ Function.support x →
      Function.support x ⊆ Function.support y)
    (z : Fin n → ℝ) (hAz : A z = 0)
    (hzx : Function.support z ⊆ Function.support x) :
    ∃ t : ℝ, z = t • x := by
  classical
  have hex : ∃ i, 0 < x i := by
    by_contra h
    push_neg at h
    apply hxne
    funext i
    exact le_antisymm (h i) (hx i)
  let s : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, by simp [s, ne_of_gt hi]⟩
  obtain ⟨j, hj, hratio⟩ :=
    Finset.exists_min_image s (fun i => z i / x i) hs
  have hxj : x j ≠ 0 := (Finset.mem_filter.mp hj).2
  let t : ℝ := z j / x j
  have htj : t * x j = z j := div_mul_cancel₀ _ hxj
  have hout : ∀ i, x i = 0 → z i = 0 := by
    intro i hxi
    by_contra hzi
    exact (hzx hzi) hxi
  let q : Fin n → ℝ := z - t • x
  have hq : ∀ i, 0 ≤ q i := by
    intro i
    change 0 ≤ z i - t * x i
    by_cases hxi : x i = 0
    · simp [hxi, hout i hxi]
    · have hpos : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hxi)
      have hle : t ≤ z i / x i := hratio i (by simp [s, hxi])
      have hmul : t * x i ≤ z i := (le_div_iff₀ hpos).mp hle
      linarith
  have hAq : A q = 0 := by
    simp [q, map_sub, map_smul, hAz, hAx]
  have hqsub : Function.support q ⊆ Function.support x := by
    intro i hi
    change q i ≠ 0 at hi
    change x i ≠ 0
    intro hxi
    exact hi (by simp [q, hxi, hout i hxi])
  have hqzero : q = 0 := by
    by_contra hne
    have hjq : q j ≠ 0 := (hmin q hq hAq hne hqsub) hxj
    apply hjq
    change z j - t * x j = 0
    linarith
  exact ⟨t, sub_eq_zero.mp hqzero⟩

/-- An explicit injection into range(A) × ℝ gives the sharp rank+1 cutoff. -/
theorem support_card_le_rank_add_one (n k : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : Fin n → ℝ)
    (hxne : x ≠ 0)
    (hline : ∀ z : Fin n → ℝ, A z = 0 →
      Function.support z ⊆ Function.support x → ∃ t : ℝ, z = t • x) :
    Nat.card {i : Fin n // x i ≠ 0} ≤ Module.finrank ℝ (LinearMap.range A) + 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hxne (funext h)
  let S := {i : Fin n // x i ≠ 0}
  let e : (S → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun v i => if h : x i ≠ 0 then v ⟨i, h⟩ else 0
      map_add' := by
        intro u v
        funext i
        by_cases h : x i ≠ 0
        · simp [h]
        · have hx0 : x i = 0 := by simpa using h
          simp [h, hx0]
      map_smul' := by
        intro r v
        funext i
        by_cases h : x i ≠ 0 <;> simp [h] }
  let f : (S → ℝ) →ₗ[ℝ] (LinearMap.range A × ℝ) :=
    { toFun := fun v => (⟨A (e v), ⟨e v, rfl⟩⟩, (e v) j)
      map_add' := by
        intro u v
        apply Prod.ext
        · apply Subtype.ext
          change A (e (u + v)) = A (e u) + A (e v)
          simp only [map_add]
        · change (e (u + v)) j = (e u) j + (e v) j
          simp only [map_add, Pi.add_apply]
      map_smul' := by
        intro r v
        apply Prod.ext
        · apply Subtype.ext
          change A (e (r • v)) = r • A (e v)
          simp only [map_smul, RingHom.id_apply]
        · change (e (r • v)) j = r • (e v) j
          simp only [map_smul, RingHom.id_apply, Pi.smul_apply] }
  have hf : Function.Injective f := by
    intro u v huv
    have hfzero : f (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have hA : A (e (u - v)) = 0 :=
      congrArg (fun w : LinearMap.range A × ℝ => (w.1 : Fin k → ℝ)) hfzero
    have hjzero : (e (u - v)) j = 0 := congrArg Prod.snd hfzero
    have hsub : Function.support (e (u - v)) ⊆ Function.support x := by
      intro i hi
      change (e (u - v)) i ≠ 0 at hi
      change x i ≠ 0
      intro hxi
      exact hi (by simp [e, hxi])
    obtain ⟨t, ht⟩ := hline (e (u - v)) hA hsub
    have htzero : t = 0 := by
      have hval := congrFun ht j
      change (e (u - v)) j = t * x j at hval
      have hm : t * x j = 0 := hval.symm.trans hjzero
      exact (mul_eq_zero.mp hm).resolve_right hj
    have hezero : e (u - v) = 0 := by rw [ht, htzero, zero_smul]
    funext i
    have hi := congrFun hezero i.1
    have hz : u i - v i = 0 := by simpa [e, i.property] using hi
    exact sub_eq_zero.mp hz
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  simpa only [Module.finrank_fintype_fun_eq_card, Module.finrank_prod,
    Module.finrank_self, Nat.card_eq_fintype_card] using hd

end Hirsch.PositiveCircuitRank

/-- Minimal positive dependence is equivalent to one-dimensional signed kernel
on the support, and every such support has at most rank(A)+1 coordinates. -/
theorem solution (n k : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hAx : A x = 0) (hxne : x ≠ 0) :
    ((∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → A y = 0 → y ≠ 0 →
        Function.support y ⊆ Function.support x →
        Function.support x ⊆ Function.support y) ↔
      (∀ z : Fin n → ℝ, A z = 0 →
        Function.support z ⊆ Function.support x → ∃ t : ℝ, z = t • x)) ∧
    ((∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → A y = 0 → y ≠ 0 →
        Function.support y ⊆ Function.support x →
        Function.support x ⊆ Function.support y) →
      Nat.card {i : Fin n // x i ≠ 0} ≤ Module.finrank ℝ (LinearMap.range A) + 1) := by
  constructor
  · constructor
    · exact Hirsch.PositiveCircuitRank.signed_ray_of_minimal n k A x hx hAx hxne
    · intro hline y _hy hAy hyne hyx
      obtain ⟨t, ht⟩ := hline y hAy hyx
      have htne : t ≠ 0 := by
        intro htz
        apply hyne
        rw [ht, htz, zero_smul]
      intro i hi
      change y i ≠ 0
      rw [ht]
      change t * x i ≠ 0
      exact mul_ne_zero htne hi
  · intro hmin
    exact Hirsch.PositiveCircuitRank.support_card_le_rank_add_one n k A x hxne
      (Hirsch.PositiveCircuitRank.signed_ray_of_minimal n k A x hx hAx hxne hmin)

#print axioms Hirsch.PositiveCircuitRank.signed_ray_of_minimal
#print axioms Hirsch.PositiveCircuitRank.support_card_le_rank_add_one
#print axioms solution
