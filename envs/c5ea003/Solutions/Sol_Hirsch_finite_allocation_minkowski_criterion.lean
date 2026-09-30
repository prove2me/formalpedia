-- Prove2me | solution 1 for Hirsch.finite_allocation_minkowski_criterion
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-13T20:33:37.704295+00:00
-- url     : https://prove2.me/submissions/f5304244-5800-46f7-b0c5-98cdf4c6d71a

import Mathlib

open scoped BigOperators

/-! Finite positive-circuit completeness for linear tests on a nonnegative kernel.
No feasibility, Farkas, circuit-generation, or diameter theorem is assumed.
-/

namespace Hirsch.PositiveCircuitTests

noncomputable def supp {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) : Finset (ι) := by
  classical
  exact Finset.univ.filter (fun i => x i ≠ 0)

@[simp] theorem mem_supp {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) (i : ι) :
    i ∈ supp x ↔ x i ≠ 0 := by
  classical
  simp [supp]

def NonnegNull {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (A : (ι → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ A x = 0

def Circuit {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (A : (ι → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : ι → ℝ) : Prop :=
  NonnegNull A x ∧ x ≠ 0 ∧
    ∀ y, NonnegNull A y → y ≠ 0 → supp y ⊆ supp x → supp x ⊆ supp y

private theorem positive_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hne : x ≠ 0) : ∃ i, 0 < x i := by
  by_contra h
  push_neg at h
  apply hne
  funext i
  exact le_antisymm (h i) (hx i)

/-- Subtract as far as possible in a supported direction with a positive entry. -/
private theorem prune {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsub : supp y ⊆ supp x)
    (hy : ∃ i, 0 < y i) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ (x - t • y) i) ∧
      supp (x - t • y) ⊂ supp x := by
  classical
  let s : Finset (ι) := Finset.univ.filter (fun i => 0 < y i)
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
theorem negative_circuit {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (A : (ι → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (b : (ι → ℝ) →ₗ[ℝ] ℝ) (w : ι → ℝ)
    (hw : NonnegNull A w) (hb : b w < 0) :
    ∃ x, Circuit A x ∧ b x < 0 ∧ supp x ⊆ supp w := by
  classical
  let P : ℕ → Prop := fun q => ∃ x : ι → ℝ,
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
theorem same_support_ray {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (A : (ι → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (x y : ι → ℝ) (hx : Circuit A x) (hy : NonnegNull A y)
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
theorem finite_tests {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (A : (ι → ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ c : Finset (ι) → (ι → ℝ),
      (∀ s, c s = 0 ∨ Circuit A (c s) ∧ supp (c s) = s) ∧
      ∀ b : (ι → ℝ) →ₗ[ℝ] ℝ,
        (∀ x, NonnegNull A x → 0 ≤ b x) ↔ ∀ s, 0 ≤ b (c s) := by
  classical
  let Has : Finset (ι) → Prop := fun s =>
    ∃ x : ι → ℝ, Circuit A x ∧ supp x = s
  let c : Finset (ι) → (ι → ℝ) :=
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

open Set

private theorem compact_positive_of_tests
    (m : ℕ) (K : Set (Fin m → ℝ))
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (htest : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
      ∃ x ∈ K, 0 ≤ ∑ i, w i * x i) :
    ∃ x ∈ K, ∀ i, 0 ≤ x i := by
  classical
  by_contra hn
  have hd : Disjoint K (ProperCone.positive ℝ (Fin m → ℝ) : Set (Fin m → ℝ)) := by
    apply Set.disjoint_left.mpr
    intro x hx hpos
    exact hn ⟨x, hx, ProperCone.mem_positive.mp hpos⟩
  obtain ⟨f, hf, hneg⟩ :=
    (ProperCone.positive ℝ (Fin m → ℝ)).hyperplane_separation hconv hK hd
  let w : Fin m → ℝ := fun i => f (Pi.single i (1 : ℝ))
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    apply hf
    change (0 : Fin m → ℝ) ≤ Pi.single i (1 : ℝ)
    intro j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Pi.single_apply, hij, Ne.symm hij]
  obtain ⟨x, hx, hsum⟩ := htest w hw
  have hexp : (∑ i : Fin m, x i • (Pi.single i (1 : ℝ))) = x := by
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite]
  have hfx : f x = ∑ i, w i * x i := by
    calc
      f x = f (∑ i : Fin m, x i • (Pi.single i (1 : ℝ))) := congrArg f hexp.symm
      _ = ∑ i, x i * w i := by simp [w, map_sum, map_smul, smul_eq_mul]
      _ = ∑ i, w i * x i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact mul_comm _ _
  have hlt := hneg x hx
  rw [hfx] at hlt
  exact (not_lt_of_ge hsum) hlt

private theorem compact_linear_feasible_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (Q : Set E) (hQ : IsCompact Q) (hconv : Convex ℝ Q)
    (a : Fin m → E →L[ℝ] ℝ) (b : Fin m → ℝ) :
    (∃ q ∈ Q, ∀ i, b i ≤ a i q) ↔
      (∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
        ∃ q ∈ Q, (∑ i, w i * b i) ≤ ∑ i, w i * a i q) := by
  constructor
  · rintro ⟨q, hq, hbound⟩ w hw
    exact ⟨q, hq, Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hbound i) (hw i))⟩
  · intro htest
    let φ : E → (Fin m → ℝ) := fun q i => a i q - b i
    have hcont : Continuous φ := by
      apply continuous_pi
      intro i
      exact (a i).continuous.sub continuous_const
    have hc : Convex ℝ (φ '' Q) := by
      intro u hu v hv α β hα hβ hsum
      obtain ⟨p, hp, rfl⟩ := hu
      obtain ⟨q, hq, rfl⟩ := hv
      refine ⟨α • p + β • q, hconv hp hq hα hβ hsum, ?_⟩
      funext i
      change a i (α • p + β • q) - b i =
        α * (a i p - b i) + β * (a i q - b i)
      simp only [map_add, map_smul, smul_eq_mul]
      have hconst : α * b i + β * b i = b i := by
        rw [← add_mul, hsum, one_mul]
      nlinarith
    have ht : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
        ∃ z ∈ φ '' Q, 0 ≤ ∑ i, w i * z i := by
      intro w hw
      obtain ⟨q, hq, hbound⟩ := htest w hw
      refine ⟨φ q, ⟨q, hq, rfl⟩, ?_⟩
      change 0 ≤ ∑ i, w i * (a i q - b i)
      simp only [mul_sub, Finset.sum_sub_distrib]
      exact sub_nonneg.mpr hbound
    obtain ⟨z, hz, hpos⟩ := compact_positive_of_tests m (φ '' Q) (hQ.image hcont) hc ht
    obtain ⟨q, hq, rfl⟩ := hz
    exact ⟨q, hq, fun i => sub_nonneg.mp (hpos i)⟩



namespace Hirsch.FiniteAllocation

/-- The bounded allocation simplex; its zero-dimensional and zero-scale cases
are included. No boundedness assumption on the original polyhedron is used. -/
def allocationSimplex (k : ℕ) (t : ℝ) : Set (Fin k → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ (∑ j, x j) ≤ t}

lemma allocationSimplex_compact (k : ℕ) (t : ℝ) :
    IsCompact (allocationSimplex k t) := by
  classical
  have heq : allocationSimplex k t =
      Set.Icc (0 : Fin k → ℝ) (fun _ => t) ∩ {x | (∑ j, x j) ≤ t} := by
    ext x
    constructor
    · rintro ⟨hx, hs⟩
      refine ⟨⟨hx, ?_⟩, hs⟩
      intro j
      exact (Finset.single_le_sum (fun i _ => hx i) (Finset.mem_univ j)).trans hs
    · rintro ⟨⟨hx, _⟩, hs⟩
      exact ⟨hx, hs⟩
  rw [heq]
  exact isCompact_Icc.inter_right (isClosed_le (by fun_prop) continuous_const)

lemma allocationSimplex_convex (k : ℕ) (t : ℝ) :
    Convex ℝ (allocationSimplex k t) := by
  intro x hx y hy α β hα hβ hab
  refine ⟨fun j => add_nonneg (mul_nonneg hα (hx.1 j))
    (mul_nonneg hβ (hy.1 j)), ?_⟩
  change (∑ j : Fin k, (α * x j + β * y j)) ≤ t
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h₁ := mul_le_mul_of_nonneg_left hx.2 hα
  have h₂ := mul_le_mul_of_nonneg_left hy.2 hβ
  have hc : α*t+β*t=t := by rw [← add_mul, hab, one_mul]
  linarith

lemma row_expansion {k : ℕ} (a : (Fin k → ℝ) →L[ℝ] ℝ) (x : Fin k → ℝ) :
    a x = ∑ j, a (Pi.single j (1 : ℝ)) * x j := by
  classical
  have he : (∑ j : Fin k, x j • Pi.single j (1 : ℝ)) = x := by
    funext i
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite]
  calc
    a x = a (∑ j : Fin k, x j • Pi.single j (1 : ℝ)) := congrArg a he.symm
    _ = ∑ j, a (Pi.single j (1 : ℝ)) * x j := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, smul_eq_mul, mul_comm]

lemma weighted_expansion {m k : ℕ}
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ) (w : Fin m → ℝ) (x : Fin k → ℝ) :
    (∑ i, w i * a i x) =
      ∑ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) * x j := by
  calc
    (∑ i, w i * a i x) =
        ∑ i, w i * (∑ j, a i (Pi.single j (1 : ℝ)) * x j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z : ℝ => w i * z) (row_expansion (a i) x)
    _ = ∑ j, ∑ i, w i * (a i (Pi.single j (1 : ℝ)) * x j) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Construct the multiplier of the simplex-total row from the maximum of the
finitely many negative coefficients. This derives, rather than assumes, the
bounded allocation alternative needed after compact separation. -/
lemma weighted_simplex_minimum {m k : ℕ}
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ) (w : Fin m → ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ (μ : Fin k → ℝ) (ν : ℝ) (x : Fin k → ℝ),
      (∀ j, 0 ≤ μ j) ∧ 0 ≤ ν ∧ x ∈ allocationSimplex k t ∧
      (∀ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) - μ j + ν = 0) ∧
      (∑ i, w i * a i x) = -ν*t := by
  classical
  let r : Fin k → ℝ := fun j => ∑ i, w i * a i (Pi.single j (1 : ℝ))
  let f : Option (Fin k) → ℝ := fun j => match j with
    | none => 0
    | some j => -r j
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Option (Fin k))) f ⟨none, Finset.mem_univ _⟩
  let ν := f j
  have hν : 0 ≤ ν := hmax none (Finset.mem_univ _)
  have hμ : ∀ i, 0 ≤ r i + ν := by
    intro i
    have hh : -r i ≤ ν := hmax (some i) (Finset.mem_univ _)
    linarith
  refine ⟨fun i => r i + ν, ν, ?_⟩
  cases j with
  | none =>
    refine ⟨0, hμ, hν, ⟨by simp, by simpa using ht⟩, ?_, ?_⟩
    · intro i
      change r i - (r i + ν) + ν = 0
      ring
    · simp [ν, f]
  | some j =>
    refine ⟨t • Pi.single j (1 : ℝ), hμ, hν, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro i
        by_cases hi : j = i
        · subst i
          simpa using ht
        · simp [Pi.smul_apply, Pi.single_apply, hi, Ne.symm hi]
      · change (∑ i : Fin k, t * (Pi.single j (1 : ℝ) : Fin k → ℝ) i) ≤ t
        simp [Pi.single_apply, mul_ite]
    · intro i
      change r i - (r i + ν) + ν = 0
      ring
    · simp only [map_smul, smul_eq_mul]
      calc
        (∑ i, w i * (t * a i (Pi.single j (1 : ℝ)))) =
            t * (∑ i, w i * a i (Pi.single j (1 : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = -ν*t := by dsimp [ν, f, r]; ring

/-- Full feasibility equivalence for the bounded simplex allocation system.
The sufficiency direction is proved from the compact separation core of #216,
not introduced as a Farkas axiom. -/
theorem allocation_alternative {m k : ℕ}
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ) (b : Fin m → ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    (∃ x ∈ allocationSimplex k t, ∀ i, a i x ≤ b i) ↔
      ∀ (w : Fin m → ℝ) (μ : Fin k → ℝ) (ν : ℝ),
        (∀ i, 0 ≤ w i) → (∀ j, 0 ≤ μ j) → 0 ≤ ν →
        (∀ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) - μ j + ν = 0) →
        0 ≤ (∑ i, w i * b i) + ν*t := by
  constructor
  · rintro ⟨x, hx, hax⟩ w μ ν hw hμ hν hker
    have hweighted : (∑ i, w i * a i x) ≤ ∑ i, w i * b i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hax i) (hw i))
    have heq : (∑ i, w i * a i x) =
        (∑ j, μ j * x j) - ν*(∑ j, x j) := by
      rw [weighted_expansion]
      calc
        (∑ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) * x j) =
            ∑ j, (μ j - ν) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          have hh := hker j
          congr 1
          linarith
        _ = _ := by simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    have hpositive : 0 ≤ ∑ j, μ j * x j :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hμ j) (hx.1 j))
    have hbudget := mul_le_mul_of_nonneg_left hx.2 hν
    linarith
  · intro hdual
    have htests : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
        ∃ x ∈ allocationSimplex k t,
          (∑ i, w i * (-b i)) ≤ ∑ i, w i * (-(a i) x) := by
      intro w hw
      obtain ⟨μ, ν, x, hμ, hν, hx, hker, hval⟩ := weighted_simplex_minimum a w t ht
      have hh := hdual w μ ν hw hμ hν hker
      refine ⟨x, hx, ?_⟩
      simp only [ContinuousLinearMap.neg_apply, mul_neg, Finset.sum_neg_distrib]
      linarith
    obtain ⟨x, hx, hax⟩ :=
      (compact_linear_feasible_iff m (allocationSimplex k t)
        (allocationSimplex_compact k t) (allocationSimplex_convex k t)
        (fun i => -(a i)) (fun i => -b i)).mpr htests
    exact ⟨x, hx, fun i => by have hh := hax i; simpa using hh⟩

/-- Transpose of the allocation rows (a,-I,ones), with all original rows retained. -/
def dualMap {m k : ℕ} (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ) :
    ((Fin m ⊕ Option (Fin k)) → ℝ) →ₗ[ℝ] (Fin k → ℝ) where
  toFun w j := (∑ i, w (.inl i) * a i (Pi.single j (1 : ℝ))) -
    w (.inr (some j)) + w (.inr none)
  map_add' u v := by
    funext j
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' r w := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]
    ring

/-- Pair an allocation multiplier with the right side (b,0,t). -/
def dualBudget {m k : ℕ} (b : Fin m → ℝ) (t : ℝ) :
    ((Fin m ⊕ Option (Fin k)) → ℝ) →ₗ[ℝ] ℝ where
  toFun w := (∑ i, w (.inl i) * b i) + w (.inr none)*t
  map_add' u v := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' r w := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]
    ring

/-- One family, chosen before b and t, is sufficient for actual primal allocation.
This composes the accepted support-elimination proof with the new alternative. -/
theorem finite_allocation_tests (m k : ℕ)
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ) :
    ∃ c : Finset (Fin m ⊕ Option (Fin k)) → ((Fin m ⊕ Option (Fin k)) → ℝ),
      (∀ s, (∀ i, 0 ≤ c s i) ∧ dualMap a (c s) = 0) ∧
      ∀ (b : Fin m → ℝ) (t : ℝ), 0 ≤ t →
        ((∃ x ∈ allocationSimplex k t, ∀ i, a i x ≤ b i) ↔
          ∀ s, 0 ≤ dualBudget (k := k) b t (c s)) := by
  classical
  obtain ⟨c, hc, htest⟩ := Hirsch.PositiveCircuitTests.finite_tests (dualMap a)
  have hcnull : ∀ s, (∀ i, 0 ≤ c s i) ∧ dualMap a (c s) = 0 := by
    intro s
    rcases hc s with hz | ⟨hs, _⟩
    · simp [hz]
    · exact hs.1
  refine ⟨c, hcnull, ?_⟩
  intro b t ht
  rw [allocation_alternative a b t ht]
  constructor
  · intro h s
    exact h (fun i => c s (.inl i)) (fun j => c s (.inr (some j)))
      (c s (.inr none)) (fun i => (hcnull s).1 _) (fun j => (hcnull s).1 _)
      ((hcnull s).1 _) (fun j => congrFun (hcnull s).2 j)
  · intro h w μ ν hw hμ hν hker
    let z : (Fin m ⊕ Option (Fin k)) → ℝ :=
      Sum.elim w (fun j => match j with | none => ν | some j => μ j)
    have hz : ∀ i, 0 ≤ z i := by
      intro i
      cases i with
      | inl i => exact hw i
      | inr j => cases j with
        | none => exact hν
        | some j => exact hμ j
    have hzA : dualMap a z = 0 := by
      funext j
      exact hker j
    have hh := (htest (dualBudget (k := k) b t)).mpr h z ⟨hz, hzA⟩
    exact hh

end Hirsch.FiniteAllocation

/-- A finite null-certificate family proves whole-set Minkowski reconstruction
for an arbitrary finite-generator image of a bounded allocation simplex.
The family is fixed before the original RHS, support bounds and scale. -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m k : ℕ) (a : Fin m → E →L[ℝ] ℝ)
    (G : (Fin k → ℝ) →L[ℝ] E) :
    ∃ c : Finset (Fin m ⊕ Option (Fin k)) → ((Fin m ⊕ Option (Fin k)) → ℝ),
      (∀ s, (∀ i, 0 ≤ c s i) ∧
        ∀ j, -(∑ i, c s (.inl i) * a i (G (Pi.single j (1 : ℝ)))) -
          c s (.inr (some j)) + c s (.inr none) = 0) ∧
      ∀ (b h : Fin m → ℝ) (t : ℝ), 0 ≤ t →
        (∀ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) → (∑ j, θ j) ≤ t →
          ∀ i, a i (G θ) ≤ h i) →
        (({x : E | ∀ i, a i x ≤ b i} =
          {x : E | ∃ p : E, (∀ i, a i p ≤ b i - h i) ∧
            ∃ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) ∧ (∑ j, θ j) ≤ t ∧ p + G θ = x}) ↔
        (∀ x : E, (∀ i, a i x ≤ b i) → ∀ s,
          0 ≤ (∑ i, c s (.inl i) * (b i - a i x - h i)) + c s (.inr none)*t)) := by
  classical
  let f : Fin m → (Fin k → ℝ) →L[ℝ] ℝ := fun i => -(a i).comp G
  obtain ⟨c, hc, htest⟩ := Hirsch.FiniteAllocation.finite_allocation_tests m k f
  refine ⟨c, ?_, ?_⟩
  · intro s
    refine ⟨(hc s).1, ?_⟩
    intro j
    have hh := congrFun (hc s).2 j
    simpa only [Hirsch.FiniteAllocation.dualMap, f, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, mul_neg, Finset.sum_neg_distrib, Pi.zero_apply] using hh
  · intro b h t ht hsupport
    constructor
    · intro heq x hx
      have hx' : x ∈ {z : E | ∃ p : E, (∀ i, a i p ≤ b i - h i) ∧
          ∃ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) ∧ (∑ j, θ j) ≤ t ∧ p + G θ = z} := by
        rw [← heq]
        exact hx
      obtain ⟨p, hp, θ, hθ, hsum, he⟩ := hx'
      have hfeas : ∃ θ ∈ Hirsch.FiniteAllocation.allocationSimplex k t,
          ∀ i, f i θ ≤ b i - a i x - h i := by
        refine ⟨θ, ⟨hθ, hsum⟩, ?_⟩
        intro i
        change -a i (G θ) ≤ b i - a i x - h i
        rw [← he, map_add]
        have hi := hp i
        linarith
      exact (htest (fun i => b i - a i x - h i) t ht).mp hfeas
    · intro hfinite
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨θ, hθ, hbound⟩ :=
          (htest (fun i => b i - a i x - h i) t ht).mpr (hfinite x hx)
        refine ⟨x - G θ, ?_, θ, hθ.1, hθ.2, sub_add_cancel x (G θ)⟩
        intro i
        rw [map_sub]
        have hh : -a i (G θ) ≤ b i - a i x - h i := hbound i
        linarith
      · rintro x ⟨p, hp, θ, hθ, hsum, rfl⟩ i
        rw [map_add]
        have hh := hsupport θ hθ hsum i
        have hh' := hp i
        linarith

#print axioms Hirsch.FiniteAllocation.allocation_alternative
#print axioms Hirsch.FiniteAllocation.finite_allocation_tests
#print axioms solution
