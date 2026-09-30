-- Prove2me | solution 1 for Hirsch.optimal_original_row_edge_charging
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-24T13:51:14.624952+00:00
-- url     : https://prove2.me/submissions/98759442-081e-4d9a-b0b6-f59cf4f51140

import Mathlib

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Hirsch.HullCoordinate
open Set
variable {d : ℕ}

lemma finite_margin {ι : Type*} (S : Finset ι) (a t : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i) :
    ∃ e : ℝ, 0 < e ∧ ∀ i ∈ S, e * |t i| < a i := by
  classical
  revert ha
  induction S using Finset.induction_on with
  | empty =>
      intro ha
      exact ⟨1, by norm_num, by simp⟩
  | @insert i S hi ih =>
      intro ha
      obtain ⟨e, he, hS⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      have hai : 0 < a i := ha i (Finset.mem_insert_self i S)
      have hd : 0 < |t i| + 1 := by positivity
      let f : ℝ := a i / (|t i| + 1)
      have hf : 0 < f := div_pos hai hd
      have hfeq : f * (|t i| + 1) = a i := by
        dsimp [f]
        exact div_mul_cancel₀ _ (ne_of_gt hd)
      refine ⟨min e f, lt_min he hf, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        have hb := mul_le_mul_of_nonneg_right (min_le_right e f) (abs_nonneg (t i))
        nlinarith
      · exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right (min_le_left e f) (abs_nonneg (t j))) (hS j hj)

end Hirsch.HullCoordinate

namespace Hirsch.TargetRows
open Set
variable {d m : ℕ}

def body (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, A i x ≤ b i}

end Hirsch.TargetRows

namespace Hirsch.RadialRowEnvelope
open Set TargetRows
variable {d m : ℕ}

lemma forward_tangent_feasible (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (x z : Fin d → ℝ) (hx : x ∈ body A b)
    (hz : ∀ i, A i x = b i → A i z = 0) :
    ∃ e : ℝ, 0 < e ∧ x + e • z ∈ body A b := by
  classical
  let S := Finset.univ.filter (fun i : Fin m => A i x ≠ b i)
  have hs : ∀ i ∈ S, 0 < b i - A i x := by
    intro i hi
    exact sub_pos.mpr (lt_of_le_of_ne (hx i) (Finset.mem_filter.mp hi).2)
  obtain ⟨e, he, hsmall⟩ := HullCoordinate.finite_margin S
    (fun i => b i - A i x) (fun i => A i z) hs
  refine ⟨e, he, ?_⟩
  intro i
  by_cases hi : A i x = b i
  · simp only [map_add, map_smul, smul_eq_mul, hz i hi, mul_zero, add_zero]
    exact hx i
  · have hb := hsmall i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    have hab := mul_le_mul_of_nonneg_left (le_abs_self (A i z)) he.le
    simp only [map_add, map_smul, smul_eq_mul]
    linarith

theorem exposed_edge_row (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (v u w : Fin d → ℝ) (hv : v ∈ body A b)
    (hu : u ∈ body A b) (hw : w ∈ body A b)
    (hE : IsExposed ℝ (body A b) (segment ℝ u w))
    (hvout : v ∉ segment ℝ u w) :
    ∃ i : Fin m, A i v < b i ∧ A i u = b i ∧ A i w = b i := by
  classical
  obtain ⟨f, hf⟩ := hE ⟨u, left_mem_segment ℝ u w⟩
  let x := (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • w
  have hxseg : x ∈ segment ℝ u w :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hxF : x ∈ body A b ∧ ∀ z ∈ body A b, f z ≤ f x := by
    change x ∈ {z ∈ body A b | ∀ y ∈ body A b, f y ≤ f z}
    rw [← hf]
    exact hxseg
  have hgap : f v < f x := by
    apply lt_of_le_of_ne (hxF.2 v hv)
    intro he
    apply hvout
    rw [hf]
    exact ⟨hv, fun z hz => by rw [he]; exact hxF.2 z hz⟩
  by_contra hn
  have hactive : ∀ i, A i x = b i → A i v = b i := by
    intro i hi
    have hm : A i x = (A i u + A i w) / 2 := by
      dsimp [x]
      simp only [map_add, map_smul, smul_eq_mul]
      ring
    have hu' : A i u = b i := by linarith [hu i, hw i]
    have hw' : A i w = b i := by linarith [hu i, hw i]
    by_contra hi'
    exact hn ⟨i, lt_of_le_of_ne (hv i) hi', hu', hw'⟩
  obtain ⟨e, he, hs⟩ := forward_tangent_feasible A b x (x - v) hxF.1 (by
    intro i hi
    rw [map_sub, hi, hactive i hi, sub_self])
  have hmax := hxF.2 (x + e • (x - v)) hs
  simp only [map_add, map_smul, map_sub, smul_eq_mul] at hmax
  have hp := mul_pos he (sub_pos.mpr hgap)
  linarith

lemma extreme_not_in_other_segment (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (v u w : Fin d → ℝ)
    (hv : v ∈ (body A b).extremePoints ℝ)
    (hu : u ∈ body A b) (hw : w ∈ body A b)
    (huv : u ≠ v) (hwv : w ≠ v) : v ∉ segment ℝ u w := by
  intro hs
  obtain ⟨a, c, ha, hc, hac, he⟩ := hs
  by_cases ha0 : a = 0
  · have hc1 : c = 1 := by linarith
    exact hwv (by simpa only [ha0, hc1, zero_smul, one_smul, zero_add] using he)
  by_cases hc0 : c = 0
  · have ha1 : a = 1 := by linarith
    exact huv (by simpa only [hc0, ha1, zero_smul, one_smul, add_zero] using he)
  have ho : v ∈ openSegment ℝ u w :=
    ⟨a, c, lt_of_le_of_ne ha (Ne.symm ha0), lt_of_le_of_ne hc (Ne.symm hc0), hac, he⟩
  exact huv (hv.2 hu hw ho)

end Hirsch.RadialRowEnvelope

namespace Hirsch.CapacitatedRows

variable {N m : ℕ}

noncomputable def forced (S : Fin N → Finset (Fin m))
    (J : Finset (Fin m)) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun t => S t ⊆ J)

noncomputable def load (f : Fin N → Fin m) (i : Fin m) : ℕ := by
  classical
  exact (Finset.univ.filter (fun t => f t = i)).card

def Capacity (S : Fin N → Finset (Fin m)) (k : ℕ) : Prop :=
  ∃ f : Fin N → Fin m, (∀ t, f t ∈ S t) ∧ ∀ i, load f i ≤ k

/-- Every edge forced into J must consume one of J's row slots. -/
lemma forced_le (S : Fin N → Finset (Fin m)) (k : ℕ)
    (f : Fin N → Fin m) (hf : ∀ t, f t ∈ S t)
    (hload : ∀ i, load f i ≤ k) (J : Finset (Fin m)) :
    (forced S J).card ≤ k * J.card := by
  classical
  let F := forced S J
  have hpartition : F.card = ∑ i ∈ J, (F.filter (fun t => f t = i)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    have hiJ : f t ∈ J := (Finset.mem_filter.mp ht).2 (hf t)
    simp [hiJ, eq_comm]
  calc
    (forced S J).card = ∑ i ∈ J, (F.filter (fun t => f t = i)).card := hpartition
    _ ≤ ∑ _i ∈ J, k := by
      apply Finset.sum_le_sum
      intro i hi
      apply le_trans _ (hload i)
      apply Finset.card_le_card
      intro t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2⟩
    _ = k * J.card := by simp [Nat.mul_comm]

/-- Capacitated Hall, written on original row subsets rather than an expanded
vertex catalogue. The finite slots are proof bookkeeping only. -/
theorem capacity_iff (S : Fin N → Finset (Fin m)) (I : Finset (Fin m))
    (hSI : ∀ t, S t ⊆ I) (k : ℕ) :
    Capacity S k ↔ ∀ J ⊆ I, (forced S J).card ≤ k * J.card := by
  classical
  constructor
  · rintro ⟨f, hf, hload⟩ J hJI
    exact forced_le S k f hf hload J
  · intro hcap
    let T : Fin N → Finset (Fin m × Fin k) :=
      fun t => (S t).product Finset.univ
    have hHall : ∀ E : Finset (Fin N), E.card ≤ (E.biUnion T).card := by
      intro E
      let J := E.biUnion S
      have hJI : J ⊆ I := by
        intro i hi
        obtain ⟨t, ht, hi⟩ := Finset.mem_biUnion.mp hi
        exact hSI t hi
      have hEF : E ⊆ forced S J := by
        intro t ht
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro i hi
        exact Finset.mem_biUnion.mpr ⟨t, ht, hi⟩
      have hslots : E.biUnion T = J.product (Finset.univ : Finset (Fin k)) := by
        ext z
        simp [T, J]
      rw [hslots, Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_fin]
      exact (Finset.card_le_card hEF).trans (by simpa only [Nat.mul_comm] using hcap J hJI)
    obtain ⟨g, hginj, hg⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective T).mp hHall
    let f : Fin N → Fin m := fun t => (g t).1
    refine ⟨f, ?_, ?_⟩
    · intro t
      exact (Finset.mem_product.mp (hg t)).1
    · intro i
      let F := Finset.univ.filter (fun t : Fin N => f t = i)
      have hinj : Set.InjOn (fun t => (g t).2) (F : Set (Fin N)) := by
        intro x hx y hy he
        apply hginj
        apply Prod.ext
        · exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
        · exact he
      change F.card ≤ k
      calc
        F.card = (F.image (fun t => (g t).2)).card :=
          (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ : Finset (Fin k)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = k := by simp

lemma capacity_N (S : Fin N → Finset (Fin m)) (hS : ∀ t, (S t).Nonempty) :
    Capacity S N := by
  classical
  choose f hf using hS
  refine ⟨f, hf, ?_⟩
  intro i
  unfold load
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card (Finset.filter_subset (fun t => f t = i) Finset.univ)

/-- Derive the optimal integral congestion and a nonempty original-row overload
witness for every unsuccessful lower capacity. No small-capacity premise. -/
theorem optimum (S : Fin N → Finset (Fin m)) (I : Finset (Fin m))
    (hSI : ∀ t, S t ⊆ I) (hS : ∀ t, (S t).Nonempty) :
    ∃ K : ℕ, K ≤ N ∧ N ≤ K * I.card ∧ Capacity S K ∧
      (∀ k : ℕ, Capacity S k ↔ K ≤ k) ∧
      (∀ k : ℕ, Capacity S k ↔ ∀ J ⊆ I, (forced S J).card ≤ k * J.card) ∧
      (∀ k : ℕ, k < K → ∃ J : Finset (Fin m), J ⊆ I ∧ J.Nonempty ∧
        k * J.card < (forced S J).card ∧ (forced S J).card ≤ K * J.card) := by
  classical
  have hex : ∃ k : ℕ, Capacity S k := ⟨N, capacity_N S hS⟩
  let K := Nat.find hex
  have hK : Capacity S K := Nat.find_spec hex
  have hmin : ∀ k, Capacity S k → K ≤ k := fun k hk => Nat.find_min' hex hk
  have hKN : K ≤ N := hmin N (capacity_N S hS)
  have hFI : forced S I = Finset.univ := by
    ext t
    simp only [forced, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact hSI t
  have hcount := (capacity_iff S I hSI K).mp hK I (by intro i hi; exact hi)
  rw [hFI, Finset.card_univ, Fintype.card_fin] at hcount
  refine ⟨K, hKN, hcount, hK, ?_, (fun k => capacity_iff S I hSI k), ?_⟩
  · intro k
    constructor
    · exact hmin k
    · intro hKk
      obtain ⟨f, hf, hload⟩ := hK
      exact ⟨f, hf, fun i => (hload i).trans hKk⟩
  · intro k hk
    have hbad : ¬ ∀ J ⊆ I, (forced S J).card ≤ k * J.card := by
      intro hh
      have hle := hmin k ((capacity_iff S I hSI k).mpr hh)
      omega
    push_neg at hbad
    obtain ⟨J, hJI, hJ⟩ := hbad
    have hne : J.Nonempty := by
      by_contra hn
      have hJE : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have hFE : forced S J = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨t, ht⟩
        obtain ⟨i, hi⟩ := hS t
        have hiJ := (Finset.mem_filter.mp ht).2 hi
        rw [hJE] at hiJ
        simpa using hiJ
      rw [hFE, Finset.card_empty] at hJ
      omega
    exact ⟨J, hJI, hne, hJ, (capacity_iff S I hSI K).mp hK J hJI⟩

end Hirsch.CapacitatedRows

/-- Optimize the row labels of actual original exposed edges and derive a
forced-row bottleneck certifying every infeasible smaller capacity. -/
theorem solution (d m N : ℕ)
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (v : Fin d → ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (u w : Fin N → (Fin d → ℝ))
    (hu : ∀ t, u t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hw : ∀ t, w t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (huv : ∀ t, u t ≠ v) (hwv : ∀ t, w t ≠ v) (huw : ∀ t, u t ≠ w t)
    (hE : ∀ t, IsExposed ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
      (segment ℝ (u t) (w t))) :
    let I := @Finset.filter (Fin m) (fun i => A i v < b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    let S := fun t : Fin N => @Finset.filter (Fin m)
      (fun i => A i v < b i ∧ A i (u t) = b i ∧ A i (w t) = b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    let F := fun J : Finset (Fin m) => @Finset.filter (Fin N) (fun t => S t ⊆ J)
      (fun _ => Classical.propDecidable _) Finset.univ
    let Cap := fun k : ℕ => ∃ f : Fin N → Fin m, (∀ t, f t ∈ S t) ∧
      ∀ i : Fin m, (@Finset.filter (Fin N) (fun t => f t = i)
        (fun _ => Classical.propDecidable _) Finset.univ).card ≤ k
    ∃ K : ℕ, K ≤ N ∧ N ≤ K * I.card ∧ Cap K ∧
      (∀ k : ℕ, Cap k ↔ K ≤ k) ∧
      (∀ k : ℕ, Cap k ↔ ∀ J ⊆ I, (F J).card ≤ k * J.card) ∧
      (∀ k : ℕ, k < K → ∃ J : Finset (Fin m), J ⊆ I ∧ J.Nonempty ∧
        k * J.card < (F J).card ∧ (F J).card ≤ K * J.card) := by
  classical
  intro I S F Cap
  have hImem : ∀ i, i ∈ I ↔ A i v < b i := by
    intro i
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
  have hSmem : ∀ t i, i ∈ S t ↔
      A i v < b i ∧ A i (u t) = b i ∧ A i (w t) = b i := by
    intro t i
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hSI : ∀ t, S t ⊆ I := by
    intro t i hi
    exact (hImem i).mpr ((hSmem t i).mp hi).1
  have hS : ∀ t, (S t).Nonempty := by
    intro t
    have hout := Hirsch.RadialRowEnvelope.extreme_not_in_other_segment A b v
      (u t) (w t) hv (hu t).1 (hw t).1 (huv t) (hwv t)
    obtain ⟨i, hi⟩ := Hirsch.RadialRowEnvelope.exposed_edge_row A b v
      (u t) (w t) hv.1 (hu t).1 (hw t).1 (hE t) hout
    exact ⟨i, (hSmem t i).mpr hi⟩
  have hF : ∀ J, Hirsch.CapacitatedRows.forced S J = F J := by
    intro J
    ext t
    simp only [Hirsch.CapacitatedRows.forced, F, Finset.mem_filter]
  have hload : ∀ (f : Fin N → Fin m) (i : Fin m), Hirsch.CapacitatedRows.load f i =
      (@Finset.filter (Fin N) (fun t => f t = i)
        (fun _ => Classical.propDecidable _) Finset.univ).card := by
    intro f i
    unfold Hirsch.CapacitatedRows.load
    congr 1
    ext t
    simp only [Finset.mem_filter]
  have hCap : ∀ k, Hirsch.CapacitatedRows.Capacity S k ↔ Cap k := by
    intro k
    simp only [Hirsch.CapacitatedRows.Capacity, Cap, hload]
  simpa only [hF, hCap] using Hirsch.CapacitatedRows.optimum S I hSI hS

#print axioms Hirsch.RadialRowEnvelope.exposed_edge_row
#print axioms Hirsch.CapacitatedRows.forced_le
#print axioms Hirsch.CapacitatedRows.capacity_iff
#print axioms Hirsch.CapacitatedRows.optimum
#print axioms solution
