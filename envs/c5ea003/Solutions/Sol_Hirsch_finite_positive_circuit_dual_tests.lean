-- Prove2me | solution 1 for Hirsch.finite_positive_circuit_dual_tests
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-13T19:42:42.417985+00:00
-- url     : https://prove2.me/submissions/3fd7936c-8271-4a24-b342-d60bfd29529f

import Mathlib

open scoped BigOperators

/-! Finite positive-circuit completeness for linear tests on a nonnegative kernel.
No feasibility, Farkas, circuit-generation, or diameter theorem is assumed.
-/

namespace Hirsch.PositiveCircuitTests

noncomputable def supp {n : ℕ} (x : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => x i ≠ 0)

@[simp] theorem mem_supp {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    i ∈ supp x ↔ x i ≠ 0 := by
  classical
  simp [supp]

def NonnegNull {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ A x = 0

def Circuit {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : Fin n → ℝ) : Prop :=
  NonnegNull A x ∧ x ≠ 0 ∧
    ∀ y, NonnegNull A y → y ≠ 0 → supp y ⊆ supp x → supp x ⊆ supp y

private theorem positive_coordinate {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hne : x ≠ 0) : ∃ i, 0 < x i := by
  by_contra h
  push_neg at h
  apply hne
  funext i
  exact le_antisymm (h i) (hx i)

/-- Subtract as far as possible in a supported direction with a positive entry. -/
private theorem prune {n : ℕ} (x y : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsub : supp y ⊆ supp x)
    (hy : ∃ i, 0 < y i) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ (x - t • y) i) ∧
      supp (x - t • y) ⊂ supp x := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => 0 < y i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hy
    exact ⟨i, by simp [s, hi]⟩
  obtain ⟨i, hi, hmin⟩ :=
    Finset.exists_min_image s (fun j => x j / y j) hs
  have hyi : 0 < y i := (Finset.mem_filter.mp hi).2
  have hxi : 0 < x i := by
    have hne : x i ≠ 0 := (mem_supp x i).mp
      (hsub ((mem_supp y i).mpr (ne_of_gt hyi)))
    exact lt_of_le_of_ne (hx i) (Ne.symm hne)
  let t : ℝ := x i / y i
  have ht : 0 < t := div_pos hxi hyi
  have hti : t * y i = x i := by
    exact div_mul_cancel₀ _ (ne_of_gt hyi)
  have hz : ∀ j, 0 ≤ (x - t • y) j := by
    intro j
    change 0 ≤ x j - t * y j
    by_cases hj : 0 < y j
    · have hratio : t ≤ x j / y j := hmin j (by simp [s, hj])
      have hprod : t * y j ≤ x j := (le_div_iff₀ hj).mp hratio
      linarith
    · have hprod : t * y j ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht) (le_of_not_gt hj)
      linarith [hx j]
  have hzero : ∀ j, x j = 0 → y j = 0 := by
    intro j hj
    by_contra hj'
    exact ((mem_supp x j).mp (hsub ((mem_supp y j).mpr hj'))) hj
  have hsmall : supp (x - t • y) ⊆ supp x := by
    intro j hj
    apply (mem_supp x j).mpr
    intro hxj
    have hyj := hzero j hxj
    have hneq := (mem_supp (x - t • y) j).mp hj
    apply hneq
    change x j - t * y j = 0
    rw [hxj, hyj]
    ring
  have hiout : i ∉ supp (x - t • y) := by
    intro hi'
    have hneq := (mem_supp (x - t • y) i).mp hi'
    apply hneq
    change x i - t * y i = 0
    linarith
  refine ⟨t, ht, hz, Finset.ssubset_iff_subset_ne.mpr ⟨hsmall, ?_⟩⟩
  intro heq
  apply hiout
  rw [heq]
  exact (mem_supp x i).mpr (ne_of_gt hxi)

/-- Every strictly negative nonnegative null certificate has a negative positive
circuit inside its support. Minimality concerns ALL nonnegative null vectors,
not just the negative ones. -/
theorem negative_circuit {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (b : (Fin n → ℝ) →ₗ[ℝ] ℝ) (w : Fin n → ℝ)
    (hw : NonnegNull A w) (hb : b w < 0) :
    ∃ x, Circuit A x ∧ b x < 0 ∧ supp x ⊆ supp w := by
  classical
  let P : ℕ → Prop := fun q => ∃ x : Fin n → ℝ,
    NonnegNull A x ∧ b x < 0 ∧ supp x ⊆ supp w ∧ (supp x).card = q
  have hex : ∃ q, P q := ⟨(supp w).card, w, hw, hb, fun _ h => h, rfl⟩
  obtain ⟨x, hx, hbx, hxw, hcard⟩ := Nat.find_spec hex
  have hminimal : ∀ y, NonnegNull A y → b y < 0 → supp y ⊆ supp w →
      (supp x).card ≤ (supp y).card := by
    intro y hy hby hyw
    rw [hcard]
    exact Nat.find_min' hex ⟨y, hy, hby, hyw, rfl⟩
  have hxne : x ≠ 0 := by
    intro h
    simpa [h] using hbx
  refine ⟨x, ⟨hx, hxne, ?_⟩, hbx, hxw⟩
  intro y hy hyne hyx
  by_cases hby : b y < 0
  · have hle := hminimal y hy hby (fun i hi => hxw (hyx hi))
    have heq : supp y = supp x := Finset.eq_of_subset_of_card_le hyx hle
    exact fun i hi => heq.symm ▸ hi
  · have hby0 : 0 ≤ b y := le_of_not_gt hby
    obtain ⟨t, ht, hz, hstrict⟩ :=
      prune x y hx.1 hyx (positive_coordinate y hy.1 hyne)
    have hzA : A (x - t • y) = 0 := by
      simp [map_sub, map_smul, hx.2, hy.2]
    have hzb : b (x - t • y) < 0 := by
      rw [map_sub, map_smul, smul_eq_mul]
      have hprod : 0 ≤ t * b y := mul_nonneg (le_of_lt ht) hby0
      linarith
    have hle := hminimal (x - t • y) ⟨hz, hzA⟩ hzb
      (fun i hi => hxw ((Finset.ssubset_iff_subset_ne.mp hstrict).1 hi))
    have hlt := Finset.card_lt_card hstrict
    omega

/-- A positive circuit has only one nonnegative null ray on its support. -/
theorem same_support_ray {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (x y : Fin n → ℝ) (hx : Circuit A x) (hy : NonnegNull A y)
    (hyne : y ≠ 0) (hsub : supp y ⊆ supp x) :
    ∃ t : ℝ, 0 < t ∧ x = t • y := by
  classical
  obtain ⟨t, ht, hz, hstrict⟩ :=
    prune x y hx.1.1 hsub (positive_coordinate y hy.1 hyne)
  have hzA : A (x - t • y) = 0 := by
    simp [map_sub, map_smul, hx.1.2, hy.2]
  have heq : x - t • y = 0 := by
    by_contra hne
    have hback := hx.2.2 (x - t • y) ⟨hz, hzA⟩ hne (Finset.ssubset_iff_subset_ne.mp hstrict).1
    have hle := Finset.card_le_card hback
    have hlt := Finset.card_lt_card hstrict
    omega
  exact ⟨t, ht, sub_eq_zero.mp heq⟩

/-- There is one fixed representative per possible circuit support. The choice
is independent of the objective, so these are genuinely finite universal tests. -/
theorem finite_tests {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ c : Finset (Fin n) → (Fin n → ℝ),
      (∀ s, c s = 0 ∨ Circuit A (c s) ∧ supp (c s) = s) ∧
      ∀ b : (Fin n → ℝ) →ₗ[ℝ] ℝ,
        (∀ x, NonnegNull A x → 0 ≤ b x) ↔ ∀ s, 0 ≤ b (c s) := by
  classical
  let Has : Finset (Fin n) → Prop := fun s =>
    ∃ x : Fin n → ℝ, Circuit A x ∧ supp x = s
  let c : Finset (Fin n) → (Fin n → ℝ) :=
    fun s => if h : Has s then Classical.choose h else 0
  have hc : ∀ s, c s = 0 ∨ Circuit A (c s) ∧ supp (c s) = s := by
    intro s
    by_cases h : Has s
    · right
      simpa only [c, dif_pos h] using Classical.choose_spec h
    · left
      simp only [c, dif_neg h]
  refine ⟨c, hc, ?_⟩
  intro b
  constructor
  · intro h s
    rcases hc s with hz | ⟨hs, _⟩
    · simp [hz]
    · exact h (c s) hs.1
  · intro h w hw
    by_contra hb
    have hbw : b w < 0 := lt_of_not_ge hb
    obtain ⟨x, hx, hbx, _⟩ := negative_circuit A b w hw hbw
    have hhas : Has (supp x) := ⟨x, hx, rfl⟩
    have hcs : Circuit A (c (supp x)) ∧ supp (c (supp x)) = supp x := by
      simpa only [c, dif_pos hhas] using Classical.choose_spec hhas
    obtain ⟨t, ht, heq⟩ := same_support_ray A x (c (supp x)) hx hcs.1.1
      hcs.1.2.1 (fun i hi => hcs.2 ▸ hi)
    have hnon : 0 ≤ b x := by
      rw [heq, map_smul, smul_eq_mul]
      exact mul_nonneg (le_of_lt ht) (h (supp x))
    exact (not_lt_of_ge hnon) hbx

end Hirsch.PositiveCircuitTests

/-- A finite family of positive circuits detects all linear inequalities on a
nonnegative kernel. There are at most 2^n slots, one per row support; unused slots
are zero. No claim of a polynomial circuit count or enumeration algorithm is made. -/
theorem solution (n k : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ c : Finset (Fin n) → (Fin n → ℝ),
      (∀ s, c s = 0 ∨
        ((∀ i, 0 ≤ c s i) ∧ A (c s) = 0 ∧ c s ≠ 0 ∧
          Function.support (c s) = (s : Set (Fin n)) ∧
          ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → A y = 0 → y ≠ 0 →
            Function.support y ⊆ Function.support (c s) →
            Function.support (c s) ⊆ Function.support y)) ∧
      ∀ b : (Fin n → ℝ) →ₗ[ℝ] ℝ,
        (∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → A x = 0 → 0 ≤ b x) ↔
          ∀ s, 0 ≤ b (c s) := by
  classical
  obtain ⟨c, hc, htest⟩ := Hirsch.PositiveCircuitTests.finite_tests A
  refine ⟨c, ?_, ?_⟩
  · intro s
    rcases hc s with hz | ⟨hs, heq⟩
    · exact Or.inl hz
    · right
      refine ⟨hs.1.1, hs.1.2, hs.2.1, ?_, ?_⟩
      · calc
          Function.support (c s) =
              (Hirsch.PositiveCircuitTests.supp (c s) : Set (Fin n)) := by
            ext i
            simp [Hirsch.PositiveCircuitTests.supp, Function.support]
          _ = (s : Set (Fin n)) := by rw [heq]
      · intro y hy hyA hyne hyc i hi
        have hsub : Hirsch.PositiveCircuitTests.supp y ⊆
            Hirsch.PositiveCircuitTests.supp (c s) := by
          intro j hj
          apply (Hirsch.PositiveCircuitTests.mem_supp (c s) j).mpr
          exact hyc ((Hirsch.PositiveCircuitTests.mem_supp y j).mp hj)
        exact (Hirsch.PositiveCircuitTests.mem_supp y i).mp
          (hs.2.2 y ⟨hy, hyA⟩ hyne hsub
            ((Hirsch.PositiveCircuitTests.mem_supp (c s) i).mpr hi))
  · intro b
    simpa only [Hirsch.PositiveCircuitTests.NonnegNull, and_imp] using htest b

#print axioms Hirsch.PositiveCircuitTests.negative_circuit
#print axioms Hirsch.PositiveCircuitTests.same_support_ray
#print axioms Hirsch.PositiveCircuitTests.finite_tests
#print axioms solution
