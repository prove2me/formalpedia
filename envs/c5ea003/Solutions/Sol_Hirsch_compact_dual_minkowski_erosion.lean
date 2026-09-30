-- Prove2me | solution 1 for Hirsch.compact_dual_minkowski_erosion
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-13T19:09:42.924462+00:00
-- url     : https://prove2.me/submissions/2976ce68-c33c-4cab-b48e-8a7f46be211a

import Mathlib

open Set
open scoped BigOperators

/-!
A compact-convex theorem of the alternative, followed by the whole-set
Minkowski erosion criterion. The converse is proved from Mathlib's geometric
separation theorem, not supplied as a Farkas or feasibility premise.
-/

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

/-- Whole-polyhedron reconstruction from every nonnegative weighted dual test.
The candidate is arbitrary compact convex, not restricted to a simplex.
No statement about a finite circuit list or a diameter bound is assumed. -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (a : Fin m → E →L[ℝ] ℝ) (b h : Fin m → ℝ)
    (Q : Set E) (hQ : IsCompact Q) (hconv : Convex ℝ Q)
    (hsupport : ∀ q ∈ Q, ∀ i, a i q ≤ h i) :
    ({x : E | ∀ i, a i x ≤ b i} =
      {x : E | ∃ p : E, (∀ i, a i p ≤ b i - h i) ∧
        ∃ q ∈ Q, p + q = x}) ↔
    (∀ x : E, (∀ i, a i x ≤ b i) →
      ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
        ∃ q ∈ Q, (∑ i, w i * (a i x + h i - b i)) ≤
          ∑ i, w i * a i q) := by
  constructor
  · intro heq x hx w hw
    have hx' : x ∈ {z : E | ∃ p : E, (∀ i, a i p ≤ b i - h i) ∧
        ∃ q ∈ Q, p + q = z} := by
      rw [← heq]
      exact hx
    obtain ⟨p, hp, q, hq, rfl⟩ := hx'
    refine ⟨q, hq, Finset.sum_le_sum (fun i _ => ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (hw i)
    rw [map_add]
    have hi := hp i
    linarith
  · intro htest
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨q, hq, hbound⟩ :=
        (compact_linear_feasible_iff m Q hQ hconv a (fun i => a i x + h i - b i)).mpr
          (htest x hx)
      refine ⟨x - q, ?_, q, hq, sub_add_cancel x q⟩
      intro i
      rw [map_sub]
      have hi := hbound i
      linarith
    · rintro x ⟨p, hp, q, hq, rfl⟩ i
      rw [map_add]
      have hpi := hp i
      have hqi := hsupport q hq i
      linarith

#print axioms solution
