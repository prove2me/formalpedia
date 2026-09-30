-- Prove2me | solution 1 for two_distance_set_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:09:26.831295+00:00
-- url     : https://prove2.me/submissions/efa57e98-3b18-4a16-acd1-4244e7caf490

import Mathlib

section
theorem moment_cancellation {I : Type*} [Fintype I] {d : ℕ}
    (x : I → Fin d → ℝ) (c : I → ℝ) (A B : ℝ)
    (h0 : ∑ a, c a = 0)
    (h1 : ∀ j, ∑ a, c a * x a j = 0)
    (h2 : ∀ j k, ∑ a, c a * x a j * x a k = 0) :
    (∑ a, ∑ b, c a * c b * ((∑ j, (x a j - x b j) ^ 2) - A) *
      ((∑ j, (x a j - x b j) ^ 2) - B)) = 0 := by
  classical
  let s (a : I) := ∑ j, (x a j) ^ 2
  let p (a b : I) := ∑ j, x a j * x b j
  have hd (a b : I) : (∑ j, (x a j - x b j) ^ 2) = s a + s b - 2 * p a b := by
    simp only [s, p, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs : ∑ a, c a * s a = 0 := by
    simp only [s, pow_two, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← mul_assoc, h2, Finset.sum_const_zero]
  have hp (a : I) : ∑ b, c b * p a b = 0 := by
    simp only [p, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    calc
      (∑ b, c b * (x a j * x b j)) = x a j * ∑ b, c b * x b j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = 0 := by rw [h1]; ring
  have hp2 (a : I) : ∑ b, c b * (p a b) ^ 2 = 0 := by
    simp only [p, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k _
    calc
      (∑ b, c b * (x a k * x b k * (x a j * x b j))) =
          (x a j * x a k) * ∑ b, c b * x b j * x b k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = 0 := by rw [h2]; ring
  have hsep (f g : I → ℝ) :
      (∑ a, ∑ b, c a * c b * f a * g b) =
        (∑ a, c a * f a) * ∑ b, c b * g b := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hleft (f : I → ℝ) : (∑ a, ∑ b, c a * c b * f a) = 0 := by
    have h := hsep f (fun _ => 1)
    simpa [h0] using h
  have hright (g : I → ℝ) : (∑ a, ∑ b, c a * c b * g b) = 0 := by
    have h := hsep (fun _ => 1) g
    simpa [h0] using h
  have hss : (∑ a, ∑ b, c a * c b * s a * s b) = 0 := by
    rw [hsep, hs, zero_mul]
  have hfp (f : I → ℝ) : (∑ a, ∑ b, c a * c b * f a * p a b) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    calc
      (∑ b, c a * c b * f a * p a b) = c a * f a * ∑ b, c b * p a b := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = 0 := by rw [hp]; ring
  have hsp : (∑ a, ∑ b, c a * c b * s b * p a b) = 0 := by
    rw [Finset.sum_comm]
    convert hfp s using 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    have hsymm : p b a = p a b := by simp only [p, mul_comm]
    rw [hsymm]
    ring
  have hpp : (∑ a, ∑ b, c a * c b * (p a b) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    simpa only [Finset.mul_sum, mul_assoc, mul_zero] using congrArg (c a * ·) (hp2 a)
  have hp' : (∑ a, ∑ b, c a * c b * p a b) = 0 := by
    simpa using hfp (fun _ => 1)
  have he (a b : I) :
      c a * c b * ((∑ j, (x a j - x b j) ^ 2) - A) *
          ((∑ j, (x a j - x b j) ^ 2) - B) =
      c a * c b * (s a) ^ 2 + c a * c b * (s b) ^ 2 +
        4 * (c a * c b * (p a b) ^ 2) + 2 * (c a * c b * s a * s b) -
        4 * (c a * c b * s a * p a b) - 4 * (c a * c b * s b * p a b) -
        (A + B) * (c a * c b * s a) - (A + B) * (c a * c b * s b) +
        (2 * (A + B)) * (c a * c b * p a b) + (A * B) * (c a * c b) := by
    rw [hd]
    ring
  simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  rw [hleft, hright, hpp, hss, hfp, hsp, hleft, hright, hp', h0]
  simp

end
open scoped BigOperators

section
def homogeneous {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : Fin (d + 1) → ℝ :=
  Fin.cases 1 x

def quadraticFeature {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    Sym2 (Fin (d + 1)) → ℝ :=
  Sym2.lift ⟨fun i j => homogeneous x i * homogeneous x j,
    fun _ _ => mul_comm _ _⟩

theorem feature_relation_moments {d : ℕ} {I : Type*} [Fintype I]
    (x : I → EuclideanSpace ℝ (Fin d)) (c : I → ℝ)
    (h : ∑ a, c a • quadraticFeature (x a) = 0) :
    (∑ a, c a = 0) ∧
      (∀ j, ∑ a, c a * x a j = 0) ∧
      (∀ j k, ∑ a, c a * x a j * x a k = 0) := by
  have hcoord (i j : Fin (d + 1)) := congr_fun h s(i, j)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, quadraticFeature,
    Sym2.lift_mk, Pi.zero_apply] at hcoord
  refine ⟨?_, ?_, ?_⟩
  · simpa [homogeneous] using hcoord 0 0
  · intro j
    simpa [homogeneous] using hcoord 0 j.succ
  · intro j k
    simpa [homogeneous, mul_assoc] using hcoord j.succ k.succ

theorem finrank_feature (d : ℕ) :
    Module.finrank ℝ (Sym2 (Fin (d + 1)) → ℝ) = (d + 2).choose 2 := by
  simp [Sym2.card, Nat.add_assoc]

theorem squared_distance_coordinates {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) :
    ∑ j, (x j - y j) ^ 2 = dist x y ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_sq_eq]
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]

end
open scoped BigOperators

section
theorem quadraticFeature_independent {d : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin d))) (alpha beta : ℝ)
    (ha : 0 < alpha) (hb : 0 < beta)
    (hdist : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = alpha ∨ dist x y = beta) :
    LinearIndependent ℝ (fun x : S => quadraticFeature x.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  obtain ⟨h0, h1, h2⟩ := feature_relation_moments (fun x : S => x.val) c hc
  have hcancel := moment_cancellation (fun x : S => fun j => x.val j) c
    (alpha ^ 2) (beta ^ 2) h0 h1 h2
  have hdiag (x y : S) :
      c x * c y * ((∑ j, (x.val j - y.val j) ^ 2) - alpha ^ 2) *
          ((∑ j, (x.val j - y.val j) ^ 2) - beta ^ 2) =
        if x = y then c x ^ 2 * (alpha ^ 2 * beta ^ 2) else 0 := by
    rw [squared_distance_coordinates]
    by_cases hxy : x = y
    · subst y
      simp only [dist_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_sub, ite_true]
      ring
    · have hvals : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
      rcases hdist x.val x.property y.val y.property hvals with h | h
      · simp [h, hxy]
      · simp [h, hxy]
  simp_rw [hdiag] at hcancel
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true] at hcancel
  rw [← Finset.sum_mul] at hcancel
  have hsquares : ∑ x, c x ^ 2 = 0 :=
    (mul_eq_zero.mp hcancel).resolve_right
      (mul_ne_zero (pow_ne_zero _ ha.ne') (pow_ne_zero _ hb.ne'))
  intro x
  have hx : c x ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sq_nonneg (c y))).mp hsquares
      x (Finset.mem_univ x)
  exact sq_eq_zero_iff.mp hx

theorem two_distance_card_le {d : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin d))) (alpha beta : ℝ)
    (ha : 0 < alpha) (hb : 0 < beta)
    (hdist : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = alpha ∨ dist x y = beta) :
    S.card ≤ (d + 2).choose 2 := by
  have h := (quadraticFeature_independent S alpha beta ha hb hdist).fintype_card_le_finrank
  simpa only [Fintype.card_coe, finrank_feature] using h

end
theorem solution (d : ℕ) (hd : 1 ≤ d) :
    ∀ (S : Finset (EuclideanSpace ℝ (Fin d))),
      (∃ alpha beta : ℝ, alpha ≠ beta ∧ 0 < alpha ∧ 0 < beta ∧
        ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = alpha ∨ dist x y = beta) →
      S.card ≤ Nat.choose (d + 2) 2 := by
  intro S ⟨alpha, beta, _, ha, hb, hdist⟩
  exact two_distance_card_le S alpha beta ha hb hdist

#check @solution
#print axioms solution
