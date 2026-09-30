-- Prove2me | solution 1 for lean_workbook_plus_66423
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T09:28:57.900858+00:00
-- url     : https://prove2.me/submissions/a6fde0fb-73a8-4fcf-a2b5-3cbebd76d5e9

import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace PositiveMultiplicativeFunctionalClassification

def Equation (f : ℝ → ℝ) : Prop :=
  ∀ x y, 0 < x → 0 < y → f x * f y = 2 * f (x + y * f x)

theorem associative_comparison {f : ℝ → ℝ}
    (hp : ∀ x, 0 < x → 0 < f x) (hf : Equation f)
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    f (y + z * f y / 2) = f (y + z * f y) := by
  have hp1 := hp 1 (by norm_num)
  have hpy := hp y hy
  have h1 := hf 1 y (by norm_num) hy
  have h2 := hf y z hy hz
  have h3 := hf (1 + y * f 1) z (by positivity) hz
  have h4 := hf 1 (y + z * f y / 2) (by norm_num) (by positivity)
  have hv : f (1 + y * f 1) = f 1 * f y / 2 := by linarith
  have ha : (1 + y * f 1) + z * f (1 + y * f 1) =
      1 + (y + z * f y / 2) * f 1 := by
    rw [hv]
    ring
  rw [ha, ← h4, hv] at h3
  apply mul_left_cancel₀ (ne_of_gt hp1)
  calc
    f 1 * f (y + z * f y / 2) = (f 1 * f y / 2) * f z := h3.symm
    _ = f 1 * (f y * f z / 2) := by ring
    _ = f 1 * f (y + z * f y) := by rw [h2]; ring

theorem translated_doubling {f : ℝ → ℝ}
    (hp : ∀ x, 0 < x → 0 < f x) (hf : Equation f)
    {y t : ℝ} (hy : 0 < y) (ht : 0 < t) : f (y + t) = f (y + 2 * t) := by
  have hfy : f y ≠ 0 := ne_of_gt (hp y hy)
  have h := associative_comparison hp hf hy
    (show 0 < 2 * t / f y by exact div_pos (by positivity) (hp y hy))
  have hcancel : (2 * t / f y) * f y = 2 * t := by field_simp
  rw [hcancel, show 2 * t / 2 = t by ring] at h
  exact h

theorem nearby_values_equal {f : ℝ → ℝ}
    (hp : ∀ x, 0 < x → 0 < f x) (hf : Equation f)
    {a b : ℝ} (_ha : 0 < a) (_hb : 0 < b) (hab : a < 2 * b) (hba : b < 2 * a) :
    f a = f b := by
  rcases lt_trichotomy a b with h | h | h
  · have he := translated_doubling hp hf
      (show 0 < 2 * a - b by linarith) (show 0 < b - a by linarith)
    rwa [show (2 * a - b) + (b - a) = a by ring,
      show (2 * a - b) + 2 * (b - a) = b by ring] at he
  · rw [h]
  · have he := translated_doubling hp hf
      (show 0 < 2 * b - a by linarith) (show 0 < a - b by linarith)
    rw [show (2 * b - a) + (a - b) = b by ring,
      show (2 * b - a) + 2 * (a - b) = a by ring] at he
    exact he.symm

theorem positive_locally_constant {f : ℝ → ℝ}
    (hp : ∀ x, 0 < x → 0 < f x) (hf : Equation f) :
    IsLocallyConstant (fun x : Set.Ioi (0 : ℝ) => f x) := by
  apply (IsLocallyConstant.iff_exists_open _).2
  intro x
  refine ⟨Subtype.val ⁻¹' Set.Ioo ((x : ℝ) / 2) (2 * (x : ℝ)),
    isOpen_Ioo.preimage continuous_subtype_val, ?_, ?_⟩
  · change (x : ℝ) / 2 < x ∧ (x : ℝ) < 2 * x
    have hx : 0 < (x : ℝ) := x.property
    constructor <;> linarith
  · intro y hy
    change (x : ℝ) / 2 < (y : ℝ) ∧ (y : ℝ) < 2 * (x : ℝ) at hy
    exact nearby_values_equal hp hf y.property x.property hy.2 (by linarith [hy.1])

theorem positive_value_two {f : ℝ → ℝ}
    (hp : ∀ x, 0 < x → 0 < f x) (hf : Equation f) :
    ∀ x, 0 < x → f x = 2 := by
  letI : PreconnectedSpace (Set.Ioi (0 : ℝ)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioi
  have hconst := positive_locally_constant hp hf
  have he : ∀ x, 0 < x → f x = f 1 := by
    intro x hx
    exact hconst.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨1, by norm_num⟩
  have hp1 := hp 1 (by norm_num)
  have h11 := hf 1 1 (by norm_num) (by norm_num)
  rw [he (1 + 1 * f 1) (by positivity)] at h11
  have hz : f 1 * (f 1 - 2) = 0 := by nlinarith
  have htwo : f 1 = 2 := by
    have hzero := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp1)
    linarith
  intro x hx
  exact (he x hx).trans htwo

theorem full_source_classification (f : ℝ → ℝ) :
    ((∀ x, 0 < x → 0 < f x) ∧ Equation f) ↔ (∀ x, 0 < x → f x = 2) := by
  constructor
  · rintro ⟨hp, hf⟩
    exact positive_value_two hp hf
  · intro h
    constructor
    · intro x hx
      rw [h x hx]
      norm_num
    · intro x y hx hy
      rw [h x hx, h y hy, h (x + y * 2) (by positivity)]

noncomputable def extension (g : ℝ → ℝ) (x : ℝ) : ℝ := if 0 < x then 2 else g x

theorem arbitrary_nonpositive_extension (g : ℝ → ℝ) :
    ((∀ x, 0 < x → 0 < extension g x) ∧ Equation (extension g)) ∧
      (∀ x, x ≤ 0 → extension g x = g x) := by
  constructor
  · apply (full_source_classification (extension g)).2
    intro x hx
    rw [extension, if_pos hx]
  · intro x hx
    rw [extension, if_neg (not_lt.mpr hx)]

theorem constant_two_model : (∀ x : ℝ, 0 < x → 0 < (2 : ℝ)) ∧ Equation (fun _ => 2) := by
  apply (full_source_classification (fun _ => 2)).2
  intro x hx
  rfl

end PositiveMultiplicativeFunctionalClassification

theorem solution : ¬ (∀ (f : ℝ → ℝ),
    (∀ x y : ℝ, (0 < x ∧ 0 < y) → f x * f y = 2 * f (x + y * f x)) →
    ∀ x : ℝ, 0 < x → f x = 1) := by
  intro h
  have hf := PositiveMultiplicativeFunctionalClassification.constant_two_model.2
  have hc := h (fun _ => 2) (fun x y hxy => hf x y hxy.1 hxy.2) 1 (by norm_num)
  norm_num at hc
