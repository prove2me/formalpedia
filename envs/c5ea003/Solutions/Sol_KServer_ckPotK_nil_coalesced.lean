-- Prove2me | solution 1 for KServer.ckPotK_nil_coalesced
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-07T10:45:01.855823+00:00
-- url     : https://prove2.me/submissions/2412ef8c-e0f0-45b6-a0dc-3249072bceca

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential_k

open KServer

namespace CKNil

/-- The work function of the empty request sequence is the matching cost of one move. -/
theorem workFn_nil' {k : ℕ} {N : Type} [MetricSpace N] (C₀ X : Config k N) :
    workFn C₀ [] X = moveCost C₀ X := by
  have hset : {c : ℝ | ∃ S : ℕ → Config k N, ServesFrom C₀ ([] : List N) S ∧
      c = (∑ j ∈ Finset.range ([] : List N).length, moveCost (S j) (S (j + 1)))
        + moveCost (S ([] : List N).length) X} = {moveCost C₀ X} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, List.length_nil, Finset.range_zero,
      Finset.sum_empty, zero_add]
    constructor
    · rintro ⟨S, ⟨hS0, -⟩, rfl⟩
      rw [hS0]
    · rintro rfl
      exact ⟨fun _ => C₀, ⟨rfl, fun j => j.elim0⟩, rfl⟩
  unfold workFn
  rw [hset, csInf_singleton]

/-- For a coalesced initial configuration the unordered work function of the empty request
sequence is the sum of the distances to the target configuration. -/
theorem workFnU_nil_const {k : ℕ} {N : Type} [MetricSpace N] (c : N) (X : Config k N) :
    workFnU (fun _ => c) [] X = ∑ j, dist c (X j) := by
  have h : ∀ π : Equiv.Perm (Fin k),
      workFn (fun _ : Fin k => c) [] (X ∘ π) = ∑ j, dist c (X j) := by
    intro π
    rw [workFn_nil']
    unfold moveCost
    exact Fintype.sum_equiv π (fun j => dist c (X (π j))) (fun j => dist c (X j)) fun _ => rfl
  show (⨅ π : Equiv.Perm (Fin k), workFn (fun _ : Fin k => c) [] (X ∘ π)) = _
  simp only [h]
  exact ciInf_const

theorem gauss_sum (k : ℕ) (Δ : ℝ) : ∑ i : Fin k, (2 * Δ * (((i : ℕ) : ℝ) + 1)) = Δ * k * (k + 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    push_cast
    ring

theorem card_le_filter (k : ℕ) (i : Fin k) :
    (Finset.univ.filter (fun j : Fin k => (j : ℕ) ≤ (i : ℕ))).card = (i : ℕ) + 1 := by
  have h : (Finset.univ.filter (fun j : Fin k => (j : ℕ) ≤ (i : ℕ))) = Finset.Iic i :=
    Finset.ext fun j => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic, Fin.le_def]
  rw [h, Fin.card_Iic]

theorem card_gt_filter (k : ℕ) (j : Fin k) :
    (Finset.univ.filter (fun i : Fin k => ¬ ((j : ℕ) ≤ (i : ℕ)))).card = (j : ℕ) := by
  have h : (Finset.univ.filter (fun i : Fin k => ¬ ((j : ℕ) ≤ (i : ℕ)))) = Finset.Iio j :=
    Finset.ext fun i => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def,
        Nat.not_le]
  rw [h, Fin.card_Iio]

/-- The anchor contributions cancel: the anchored potential of the empty request sequence at a
coalesced start does not depend on the anchors. -/
theorem anchor_sum (k : ℕ) (Δ : ℝ) (d : Fin k → ℝ) :
    (∑ j, d j)
      + ∑ i : Fin k, (∑ j : Fin k, if (j : ℕ) ≤ (i : ℕ) then 2 * Δ - d i else d j)
      = Δ * k * (k + 1) := by
  have inner : ∀ i : Fin k,
      (∑ j : Fin k, if (j : ℕ) ≤ (i : ℕ) then 2 * Δ - d i else d j)
        = (((i : ℕ) : ℝ) + 1) * (2 * Δ - d i)
          + ∑ j : Fin k, (if (j : ℕ) ≤ (i : ℕ) then 0 else d j) := by
    intro i
    have hsplit : ∀ j : Fin k,
        (if (j : ℕ) ≤ (i : ℕ) then 2 * Δ - d i else d j)
          = (if (j : ℕ) ≤ (i : ℕ) then 2 * Δ - d i else 0)
            + (if (j : ℕ) ≤ (i : ℕ) then 0 else d j) := by
      intro j; by_cases h : (j : ℕ) ≤ (i : ℕ) <;> simp [h]
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter, Finset.sum_const, card_le_filter, nsmul_eq_mul]
    push_cast
    ring
  have swap : ∑ i : Fin k, (∑ j : Fin k, if (j : ℕ) ≤ (i : ℕ) then (0 : ℝ) else d j)
      = ∑ j : Fin k, (((j : ℕ) : ℝ)) * d j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ∀ i : Fin k, (if (j : ℕ) ≤ (i : ℕ) then (0 : ℝ) else d j)
        = (if ¬ ((j : ℕ) ≤ (i : ℕ)) then d j else 0) := by
      intro i; by_cases h : (j : ℕ) ≤ (i : ℕ) <;> simp [h]
    rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.sum_filter, Finset.sum_const,
      card_gt_filter, nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun i _ => inner i, Finset.sum_add_distrib, swap]
  have main : (∑ j, d j) + ((∑ i : Fin k, ((((i : ℕ) : ℝ) + 1) * (2 * Δ - d i)))
      + ∑ j : Fin k, (((j : ℕ) : ℝ)) * d j)
      = ∑ i : Fin k, (2 * Δ * (((i : ℕ) : ℝ) + 1)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [main, gauss_sum]

end CKNil

open CKNil in
theorem solution (k : ℕ) (M : Type) [MetricSpace M] [Fintype M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ) (p : M) :
    ckPotK k M Δ hΔ0 hΔ (fun _ => p) [] = Δ * (k : ℝ) * ((k : ℝ) + 1) := by
  haveI : Nonempty M := ⟨p⟩
  have hconst : ∀ x : Fin k → M,
      ckPotAtK k M Δ hΔ0 hΔ (fun _ => p) [] x = Δ * (k : ℝ) * ((k : ℝ) + 1) := by
    intro x
    unfold ckPotAtK
    rw [List.map_nil]
    rw [@workFnU_nil_const k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (Sum.inl p)
      (fun j => Sum.inl (x j))]
    have hterm : ∀ i : Fin k,
        @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun _ => Sum.inl p) []
            (ckConfigK x i)
          = ∑ j : Fin k, if (j : ℕ) ≤ (i : ℕ) then 2 * Δ - dist p (x i) else dist p (x j) := by
      intro i
      rw [@workFnU_nil_const k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (Sum.inl p)
        (ckConfigK x i)]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : (j : ℕ) ≤ (i : ℕ) <;>
        simp [ckConfigK, h, antipodalExtension_dist]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    have hbase : ∀ j : Fin k,
        @dist (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toPseudoMetricSpace.toDist
          (Sum.inl p) (Sum.inl (x j)) = dist p (x j) := fun j => rfl
    rw [Finset.sum_congr rfl fun j _ => hbase j]
    exact anchor_sum k Δ (fun j => dist p (x j))
  unfold ckPotK
  simp only [hconst]
  exact ciInf_const
