-- Prove2me | solution 1 for Hirsch.q28_extreme_classification
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-06T01:17:27.43641+00:00
-- url     : https://prove2.me/submissions/6b4fa44d-73ed-460a-a049-25ec81d5a1ba

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert
import Theorems.Thm_Hirsch_q28_finite_certificate

open scoped RealInnerProductSpace
open Set Hirsch Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

/-! Vertex classification of the Q28 polar against the stored sign-orbits. -/

lemma four_actives_in_quotient :
    ∀ (o1 o2 : Fin 20) (s : Fin 16),
      4 ≤ commonActiveCard o1 o2 s → o1 = o2 ∨ QuotientAdj o1 o2 :=
  q28_finite_certificate.1

lemma certOkUnrank_all :
    ∀ r : ℕ, r < 2002 → certOkUnrank r = true :=
  q28_finite_certificate.2.2.2.2.1

lemma unrank_rank :
    ∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        unrank5 (combRank s0 s1 s2 s3 s4) = (s0, s1, s2, s3, s4) :=
  q28_finite_certificate.2.2.2.2.2.1

lemma combRank_lt :
    ∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        combRank s0 s1 s2 s3 s4 < 2002 :=
  q28_finite_certificate.2.2.2.2.2.2

lemma mask_bit :
    ∀ (o : Fin 20) (s : Fin 16) (i : Fin 28),
      (tightMask o s).testBit i.val = true ↔
        intDotFlip o s i = orbitDen o :=
  q28_finite_certificate.2.2.2.1

lemma potential_le_on_walk {V : Type*}
    (R : V → V → Prop) (potential : V → ℕ)
    (hstep : ∀ x y, R x y → potential y ≤ potential x + 1)
    (w : ℕ → V) (N : ℕ)
    (hw : ∀ j < N, w j = w (j + 1) ∨ R (w j) (w (j + 1))) :
    potential (w N) ≤ potential (w 0) + N := by
  have aux : ∀ j, j ≤ N → potential (w j) ≤ potential (w 0) + j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
        intro hj
        have hjN : j < N := by omega
        have hp := ih (by omega)
        have hs : potential (w (j + 1)) ≤ potential (w j) + 1 := by
          rcases hw j hjN with heq | hadj
          · rw [← heq]; omega
          · exact hstep _ _ hadj
        omega
  exact aux N le_rfl

lemma eucl_add (x y : EuclideanSpace ℝ (Fin 5)) (i : Fin 5) :
    (x + y) i = x i + y i := rfl

lemma eucl_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin 5)) (i : Fin 5) :
    (c • x) i = c * x i := rfl

lemma eucl_sub (x y : EuclideanSpace ℝ (Fin 5)) (i : Fin 5) :
    (x - y) i = x i - y i := rfl

lemma inner_single' (i : Fin 5) (c : ℝ) (x : EuclideanSpace ℝ (Fin 5)) :
    ⟪EuclideanSpace.single i c, x⟫ = c * x i := by
  simpa using EuclideanSpace.inner_single_left (𝕜 := ℝ) i c x

lemma inner_vec5 (x0 x1 x2 x3 x4 : ℝ) (x : EuclideanSpace ℝ (Fin 5)) :
    ⟪vec5 x0 x1 x2 x3 x4, x⟫ =
      x0 * x 0 + x1 * x 1 + x2 * x 2 + x3 * x 3 + x4 * x 4 := by
  simp [vec5, inner_add_left, inner_single']

lemma vec5_apply (a0 a1 a2 a3 a4 : ℝ) (j : Fin 5) :
    vec5 a0 a1 a2 a3 a4 j = ![a0, a1, a2, a3, a4] j := by
  simp [vec5, PiLp.add_apply, PiLp.single_apply]
  fin_cases j <;> simp

lemma q28A_int (i : Fin 28) (j : Fin 5) : q28A i j = (q28AZ i j : ℝ) := by
  fin_cases i <;> fin_cases j <;> simp [q28A, q28AZ, vec5_apply]

lemma det3_eq (A : Matrix (Fin 3) (Fin 3) ℤ) :
    det3 (A 0 0) (A 0 1) (A 0 2) (A 1 0) (A 1 1) (A 1 2) (A 2 0) (A 2 1) (A 2 2) =
      A.det := by
  rw [Matrix.det_fin_three]
  simp [det3]
  ring

lemma inner_midpoint (a x y : EuclideanSpace ℝ (Fin 5)) :
    ⟪a, midpoint ℝ x y⟫ = (⟪a, x⟫ + ⟪a, y⟫) / 2 := by
  rw [midpoint_eq_smul_add (R := ℝ) x y, inner_smul_right, inner_add_right, invOf_eq_inv]
  ring

lemma midpoint_coord (x y : EuclideanSpace ℝ (Fin 5)) (i : Fin 5) :
    midpoint ℝ x y i = (x i + y i) / 2 := by
  rw [midpoint_eq_smul_add (R := ℝ) x y, eucl_smul, eucl_add, invOf_eq_inv]
  ring

/-- Displacement orthogonal to every tight normal at an extreme point must vanish. -/
lemma extreme_tight_orthogonal
    {n : ℕ} {a : Fin n → EuclideanSpace ℝ (Fin 5)} {b : Fin n → ℝ}
    {x y : EuclideanSpace ℝ (Fin 5)}
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hy : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0) :
    y = 0 := by
  by_contra hy0
  have hxP : x ∈ Hpoly a b := hx.1
  let S : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, x⟫ ≠ b i)
  by_cases hS : S = ∅
  · have hyi : ∀ i, ⟪a i, y⟫ = 0 := by
      intro i
      apply hy
      by_contra hne
      have hi : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i, hne⟩
      rw [hS] at hi
      exact Finset.notMem_empty i hi
    have hp1 : x + y ∈ Hpoly a b := by
      intro i; simpa [inner_add_right, hyi i] using hxP i
    have hp2 : x - y ∈ Hpoly a b := by
      intro i; simpa [inner_sub_right, hyi i] using hxP i
    have hop : x ∈ openSegment ℝ (x - y) (x + y) := mem_openSegment_sub_add x y
    have heq : x - y = x := hx.2 hp2 hp1 hop
    have : (x - y) + y = x + y := by rw [heq]
    have hyz : y = 0 := by simpa using this
    exact hy0 hyz
  · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hS
    let δ : ℝ := S.inf' hSne (fun i => b i - ⟪a i, x⟫)
    have hδ : 0 < δ := by
      obtain ⟨iδ, hiδ, hδeq⟩ := S.exists_mem_eq_inf' hSne (fun i => b i - ⟪a i, x⟫)
      have hne : ⟪a iδ, x⟫ ≠ b iδ := (Finset.mem_filter.1 hiδ).2
      have : 0 < b iδ - ⟪a iδ, x⟫ := sub_pos.2 (lt_of_le_of_ne (hxP iδ) hne)
      simpa [δ, hδeq] using this
    let C : ℝ := ∑ i, |⟪a i, y⟫|
    have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
    let ε : ℝ := δ / (2 * (C + 1))
    have hεpos : 0 < ε := div_pos hδ (by positivity)
    have hεC : ε * C ≤ δ / 2 := by
      have hle : C ≤ C + 1 := by linarith
      have : ε * C ≤ ε * (C + 1) := mul_le_mul_of_nonneg_left hle hεpos.le
      have hden : (2 * (C + 1) : ℝ) ≠ 0 := by positivity
      have : ε * (C + 1) = δ / 2 := by
        dsimp [ε]
        field_simp [hden]
      linarith
    have hmem (σ : ℝ) (hσabs : |σ| = ε) : x + σ • y ∈ Hpoly a b := by
      intro i
      have hinner : ⟪a i, x + σ • y⟫ = ⟪a i, x⟫ + σ * ⟪a i, y⟫ := by
        simp [inner_add_right, inner_smul_right]
      rw [hinner]
      by_cases ht : ⟪a i, x⟫ = b i
      · have : ⟪a i, y⟫ = 0 := hy i ht
        simp [ht, this]
      · have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i, ht⟩
        have hslack : δ ≤ b i - ⟪a i, x⟫ := Finset.inf'_le _ hiS
        have habs : |σ * ⟪a i, y⟫| ≤ ε * C := by
          have h1 : |σ * ⟪a i, y⟫| = ε * |⟪a i, y⟫| := by simp [abs_mul, hσabs]
          have h2 : |⟪a i, y⟫| ≤ C :=
            Finset.single_le_sum (f := fun j : Fin n => |⟪a j, y⟫|)
              (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
          calc
            |σ * ⟪a i, y⟫| = ε * |⟪a i, y⟫| := h1
            _ ≤ ε * C := mul_le_mul_of_nonneg_left h2 hεpos.le
        have : σ * ⟪a i, y⟫ ≤ |σ * ⟪a i, y⟫| := le_abs_self _
        linarith
    have hp1 : x + ε • y ∈ Hpoly a b := hmem ε (abs_of_pos hεpos)
    have hp2 : x - ε • y ∈ Hpoly a b := by
      simpa [sub_eq_add_neg, neg_smul] using hmem (-ε) (by simp [abs_of_pos hεpos])
    have hop : x ∈ openSegment ℝ (x - ε • y) (x + ε • y) :=
      mem_openSegment_sub_add x (ε • y)
    have heq : x - ε • y = x := hx.2 hp2 hp1 hop
    have hyε : ε • y = 0 := by
      have : (x - ε • y) + ε • y = x + ε • y := by rw [heq]
      simpa using this
    exact hy0 ((smul_eq_zero.1 hyε).resolve_left hεpos.ne')

lemma spindle_tight_card
    {n : ℕ} {a : Fin n → EuclideanSpace ℝ (Fin 5)} {b : Fin n → ℝ}
    {x : EuclideanSpace ℝ (Fin 5)}
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    5 ≤ (Finset.univ.filter (fun i : Fin n => ⟪a i, x⟫ = b i)).card := by
  let sU : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, x⟫ = b i)
  let f : EuclideanSpace ℝ (Fin 5) →ₗ[ℝ] (sU → ℝ) :=
    LinearMap.pi fun i : sU => innerSL ℝ (a i.1)
  by_cases hbot : f.ker = ⊥
  · have hinj : Function.Injective f := LinearMap.ker_eq_bot.1 hbot
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hdE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 5 :=
      finrank_euclideanSpace_fin (𝕜 := ℝ)
    have hcod : Module.finrank ℝ (sU → ℝ) = sU.card := by simp [Fintype.card_coe]
    simpa [hdE, hcod] using hle
  · obtain ⟨z, hzker, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hyi : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, z⟫ = 0 := by
      intro i ht
      have hi : i ∈ sU := Finset.mem_filter.2 ⟨Finset.mem_univ i, ht⟩
      have hf0 : f z = 0 := LinearMap.mem_ker.1 hzker
      have : f z ⟨i, hi⟩ = 0 := by simp [hf0]
      simpa [f, innerSL] using this
    exact (hz0 (extreme_tight_orthogonal hx hyi)).elim

lemma openSegment_left_eq_of_mem_segment
    {x y p q : EuclideanSpace ℝ (Fin 5)} (hne : x ≠ y)
    (hp : p ∈ segment ℝ x y) (hq : q ∈ segment ℝ x y)
    (hopen : x ∈ openSegment ℝ p q) : p = x := by
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hopen
  obtain ⟨u, v, hu, hv, huv, hp'⟩ := hp
  obtain ⟨u', v', hu', hv', huv', hq'⟩ := hq
  have hxeq : (a * u + b * u') • x + (a * v + b * v') • y = x := by
    calc
      (a * u + b * u') • x + (a * v + b * v') • y
          = a • (u • x + v • y) + b • (u' • x + v' • y) := by
            simp only [add_smul, mul_smul, smul_add]
            abel
      _ = a • p + b • q := by rw [hp', hq']
      _ = x := hx
  have hsum : a * u + b * u' + a * v + b * v' = 1 := by
    calc
      a * u + b * u' + a * v + b * v'
          = a * (u + v) + b * (u' + v') := by ring
      _ = a * 1 + b * 1 := by rw [huv, huv']
      _ = 1 := by linarith [hab]
  have ht : a * v + b * v' = 0 := by
    have hcoeff : a * u + b * u' = 1 - (a * v + b * v') := by linarith
    have : (a * v + b * v') • (y - x) = 0 := by
      calc
        (a * v + b * v') • (y - x)
            = (a * v + b * v') • y - (a * v + b * v') • x := by rw [smul_sub]
        _ = (a * u + b * u') • x + (a * v + b * v') • y - x := by
              rw [hcoeff, sub_smul, one_smul]; abel
        _ = 0 := by simp [hxeq]
    exact (smul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne.symm)
  have hv0 : v = 0 := by
    nlinarith [mul_nonneg ha.le hv, mul_nonneg hb.le hv']
  have hu1 : u = 1 := by linarith [huv, hv0]
  calc
    p = u • x + v • y := hp'.symm
    _ = x := by simp [hu1, hv0]

lemma adj_left_extreme {P : Set (EuclideanSpace ℝ (Fin 5))} {x y}
    (h : Adj P x y) : x ∈ extremePoints ℝ P := by
  have hxseg : x ∈ extremePoints ℝ (segment ℝ x y) :=
    ⟨left_mem_segment _ _ _, fun p hp q hq hop =>
      openSegment_left_eq_of_mem_segment h.1 hp hq hop⟩
  exact h.2.extremePoints_subset_extremePoints hxseg

lemma adj_right_extreme {P : Set (EuclideanSpace ℝ (Fin 5))} {x y}
    (h : Adj P x y) : y ∈ extremePoints ℝ P :=
  adj_left_extreme ⟨h.1.symm, (segment_symm ℝ x y ▸ h.2)⟩

lemma adj_common_active_ge_four
    {x y : EuclideanSpace ℝ (Fin 5)}
    (hAdj : Adj (Hpoly q28A q28B) x y) :
    4 ≤ (Finset.univ.filter (fun i : Fin 28 =>
      ⟪q28A i, x⟫ = 1 ∧ ⟪q28A i, y⟫ = 1)).card := by
  obtain ⟨hne, hex⟩ := hAdj
  set S := Finset.univ.filter (fun i : Fin 28 => ⟪q28A i, x⟫ = 1 ∧ ⟪q28A i, y⟫ = 1)
  let f : EuclideanSpace ℝ (Fin 5) →ₗ[ℝ] (S → ℝ) :=
    LinearMap.pi fun i : S => innerSL ℝ (q28A i.1)
  have hyx_ker : y - x ∈ f.ker := by
    refine LinearMap.mem_ker.2 ?_
    ext i
    have hi := (Finset.mem_filter.1 i.2).2
    have : ⟪q28A i.1, y - x⟫ = 0 := by simp [inner_sub_right, hi.1, hi.2]
    simpa [f, innerSL] using this
  by_contra hcard
  have hle : S.card ≤ 3 := Nat.lt_succ_iff.mp (Nat.not_le.mp hcard)
  have hrankf : Module.finrank ℝ (S → ℝ) = S.card := by simp [Fintype.card_coe]
  have hker : 2 ≤ Module.finrank ℝ f.ker := by
    have hr : Module.finrank ℝ (LinearMap.range f) ≤ S.card := by
      have := Submodule.finrank_le (LinearMap.range f)
      simpa [hrankf] using this
    have hsum := LinearMap.finrank_range_add_finrank_ker f
    have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 5 :=
      finrank_euclideanSpace_fin (𝕜 := ℝ)
    omega
  have hspan_le : Submodule.span ℝ ({y - x} : Set _) ≤ f.ker := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact hyx_ker
  have hne_sub : Submodule.span ℝ ({y - x} : Set _) ≠ f.ker := by
    intro h
    have hfr : Module.finrank ℝ (Submodule.span ℝ ({y - x} : Set _)) =
        Module.finrank ℝ f.ker := by rw [h]
    have : Module.finrank ℝ (Submodule.span ℝ ({y - x} : Set _)) = 1 :=
      finrank_span_singleton (sub_ne_zero.2 hne.symm)
    omega
  obtain ⟨hv, hvker, hvspan⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hspan_le hne_sub)
  have hxP : x ∈ Hpoly q28A q28B := hex.subset (left_mem_segment _ _ _)
  have hyP : y ∈ Hpoly q28A q28B := hex.subset (right_mem_segment _ _ _)
  let m := midpoint ℝ x y
  have hmP : m ∈ Hpoly q28A q28B := hex.subset (midpoint_mem_segment _ _)
  have horth : ∀ i, ⟪q28A i, m⟫ = 1 → ⟪q28A i, hv⟫ = 0 := by
    intro i ht
    have hxle : ⟪q28A i, x⟫ ≤ 1 := by simpa [q28B] using hxP i
    have hyle : ⟪q28A i, y⟫ ≤ 1 := by simpa [q28B] using hyP i
    have hmval : ⟪q28A i, m⟫ = (⟪q28A i, x⟫ + ⟪q28A i, y⟫) / 2 := inner_midpoint _ _ _
    have hboth : ⟪q28A i, x⟫ = 1 ∧ ⟪q28A i, y⟫ = 1 := by
      have : (⟪q28A i, x⟫ + ⟪q28A i, y⟫) / 2 = 1 := by simpa [hmval] using ht
      constructor <;> linarith
    have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i, hboth⟩
    have hf0 : f hv = 0 := LinearMap.mem_ker.1 hvker
    have : f hv ⟨i, hiS⟩ = 0 := by simp [hf0]
    simpa [f, innerSL] using this
  let T : Finset (Fin 28) := Finset.univ.filter (fun i => ⟪q28A i, m⟫ ≠ 1)
  let C : ℝ := ∑ i, |⟪q28A i, hv⟫|
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases hTempty : T = ∅
  · have hall : ∀ i, ⟪q28A i, m⟫ = 1 := by
      intro i
      by_contra hne'
      have : i ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ i, hne'⟩
      rw [hTempty] at this
      exact Finset.notMem_empty i this
    have hxall : ∀ i, ⟪q28A i, x⟫ = 1 := by
      intro i
      have hxle : ⟪q28A i, x⟫ ≤ 1 := by simpa [q28B] using hxP i
      have hyle : ⟪q28A i, y⟫ ≤ 1 := by simpa [q28B] using hyP i
      have hmval : ⟪q28A i, m⟫ = (⟪q28A i, x⟫ + ⟪q28A i, y⟫) / 2 := inner_midpoint _ _ _
      have : (⟪q28A i, x⟫ + ⟪q28A i, y⟫) / 2 = 1 := by simpa [hmval] using hall i
      linarith
    have : y - x = 0 :=
      extreme_tight_orthogonal (adj_left_extreme ⟨hne, hex⟩) (fun i _ => by
        have hxle : ⟪q28A i, x⟫ ≤ 1 := by simpa [q28B] using hxP i
        have hyle : ⟪q28A i, y⟫ ≤ 1 := by simpa [q28B] using hyP i
        have hmval : ⟪q28A i, m⟫ = (⟪q28A i, x⟫ + ⟪q28A i, y⟫) / 2 := inner_midpoint _ _ _
        have : (1 + ⟪q28A i, y⟫) / 2 = 1 := by simpa [hmval, hxall i] using hall i
        have : ⟪q28A i, y⟫ = 1 := by linarith
        simp [inner_sub_right, hxall i, this])
    exact hne (sub_eq_zero.1 this).symm
  · have hT : T.Nonempty := Finset.nonempty_iff_ne_empty.2 hTempty
    let δ : ℝ := T.inf' hT (fun i => 1 - ⟪q28A i, m⟫)
    have hδ : 0 < δ := by
      obtain ⟨iδ, hiδ, hδeq⟩ := T.exists_mem_eq_inf' hT (fun i => 1 - ⟪q28A i, m⟫)
      have hne' : ⟪q28A iδ, m⟫ ≠ 1 := (Finset.mem_filter.1 hiδ).2
      have : 0 < 1 - ⟪q28A iδ, m⟫ :=
        sub_pos.2 (lt_of_le_of_ne (by simpa [q28B] using hmP iδ) hne')
      simpa [δ, hδeq] using this
    let ε : ℝ := δ / (2 * (C + 1))
    have hεpos : 0 < ε := div_pos hδ (by positivity)
    have hεC : ε * C ≤ δ / 2 := by
      have hle : C ≤ C + 1 := by linarith
      have : ε * C ≤ ε * (C + 1) := mul_le_mul_of_nonneg_left hle hεpos.le
      have hden : (2 * (C + 1) : ℝ) ≠ 0 := by positivity
      have : ε * (C + 1) = δ / 2 := by
        dsimp [ε]
        field_simp [hden]
      linarith
    have hmem (σ : ℝ) (hσabs : |σ| = ε) : m + σ • hv ∈ Hpoly q28A q28B := by
      intro i
      have hinner : ⟪q28A i, m + σ • hv⟫ = ⟪q28A i, m⟫ + σ * ⟪q28A i, hv⟫ := by
        simp [inner_add_right, inner_smul_right]
      rw [hinner]
      by_cases ht : ⟪q28A i, m⟫ = 1
      · have : ⟪q28A i, hv⟫ = 0 := horth i ht
        simp [ht, this, q28B]
      · have hiT : i ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ i, ht⟩
        have hslack : δ ≤ 1 - ⟪q28A i, m⟫ := Finset.inf'_le _ hiT
        have habs : |σ * ⟪q28A i, hv⟫| ≤ ε * C := by
          have h1 : |σ * ⟪q28A i, hv⟫| = ε * |⟪q28A i, hv⟫| := by simp [abs_mul, hσabs]
          have h2 : |⟪q28A i, hv⟫| ≤ C :=
            Finset.single_le_sum (f := fun j : Fin 28 => |⟪q28A j, hv⟫|)
              (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
          calc
            |σ * ⟪q28A i, hv⟫| = ε * |⟪q28A i, hv⟫| := h1
            _ ≤ ε * C := mul_le_mul_of_nonneg_left h2 hεpos.le
        have : σ * ⟪q28A i, hv⟫ ≤ |σ * ⟪q28A i, hv⟫| := le_abs_self _
        have : ⟪q28A i, m⟫ + σ * ⟪q28A i, hv⟫ ≤ 1 := by linarith
        simpa [q28B] using this
    have hp1 : m + ε • hv ∈ Hpoly q28A q28B := hmem ε (abs_of_pos hεpos)
    have hp2 : m - ε • hv ∈ Hpoly q28A q28B := by
      simpa [sub_eq_add_neg, neg_smul] using hmem (-ε) (by simp [abs_of_pos hεpos])
    have hop : m ∈ openSegment ℝ (m - ε • hv) (m + ε • hv) :=
      mem_openSegment_sub_add m (ε • hv)
    have hmseg : m ∈ segment ℝ x y := midpoint_mem_segment _ _
    have hleft := hex.left_mem_of_mem_openSegment hp2 hp1 hmseg hop
    obtain ⟨t, s, ht, hs, hts, hcomb⟩ := hleft
    have hs' : s = 1 - t := by linarith
    have hpar : ε • hv = (t - (2⁻¹ : ℝ)) • (y - x) := by
      ext i
      have hm_i : m i = (x i + y i) / 2 := midpoint_coord x y i
      have hcomb_i : (t • x + s • y) i = (m - ε • hv) i := by rw [hcomb]
      simp [eucl_add, eucl_smul, eucl_sub, hs'] at hcomb_i ⊢
      linarith [hm_i]
    have : hv ∈ Submodule.span ℝ ({y - x} : Set _) := by
      refine Submodule.mem_span_singleton.2 ⟨ε⁻¹ * (t - (2⁻¹ : ℝ)), ?_⟩
      have hε0 : ε ≠ 0 := hεpos.ne'
      calc
        (ε⁻¹ * (t - (2⁻¹ : ℝ))) • (y - x)
            = ε⁻¹ • ((t - (2⁻¹ : ℝ)) • (y - x)) := by simp [mul_smul]
        _ = ε⁻¹ • (ε • hv) := by rw [hpar]
        _ = hv := by simp [smul_smul, hε0]
    exact hvspan this

lemma submatrix_det3 (A : Matrix (Fin 4) (Fin 4) ℤ) (j : Fin 4) :
    (A.submatrix Fin.succ j.succAbove).det =
      det3 (A 1 (j.succAbove 0)) (A 1 (j.succAbove 1)) (A 1 (j.succAbove 2))
           (A 2 (j.succAbove 0)) (A 2 (j.succAbove 1)) (A 2 (j.succAbove 2))
           (A 3 (j.succAbove 0)) (A 3 (j.succAbove 1)) (A 3 (j.succAbove 2)) := by
  rw [← det3_eq (A.submatrix Fin.succ j.succAbove)]
  simp [Matrix.submatrix]

lemma det4_eq (A : Matrix (Fin 4) (Fin 4) ℤ) :
    A 0 0 * det3 (A 1 1) (A 1 2) (A 1 3) (A 2 1) (A 2 2) (A 2 3) (A 3 1) (A 3 2) (A 3 3)
    - A 0 1 * det3 (A 1 0) (A 1 2) (A 1 3) (A 2 0) (A 2 2) (A 2 3) (A 3 0) (A 3 2) (A 3 3)
    + A 0 2 * det3 (A 1 0) (A 1 1) (A 1 3) (A 2 0) (A 2 1) (A 2 3) (A 3 0) (A 3 1) (A 3 3)
    - A 0 3 * det3 (A 1 0) (A 1 1) (A 1 2) (A 2 0) (A 2 1) (A 2 2) (A 3 0) (A 3 1) (A 3 2)
    = A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  have hpow0 : ((-1 : ℤ) ^ ((0 : Fin 4) : ℕ)) = 1 := by decide
  have hpow1 : ((-1 : ℤ) ^ ((1 : Fin 4) : ℕ)) = -1 := by decide
  have hpow2 : ((-1 : ℤ) ^ ((2 : Fin 4) : ℕ)) = 1 := by decide
  have hpow3 : ((-1 : ℤ) ^ ((3 : Fin 4) : ℕ)) = -1 := by decide
  have s0 : (0 : Fin 4).succAbove 0 = 1 := by decide
  have s1 : (0 : Fin 4).succAbove 1 = 2 := by decide
  have s2 : (0 : Fin 4).succAbove 2 = 3 := by decide
  have t0 : (1 : Fin 4).succAbove 0 = 0 := by decide
  have t1 : (1 : Fin 4).succAbove 1 = 2 := by decide
  have t2 : (1 : Fin 4).succAbove 2 = 3 := by decide
  have u0 : (2 : Fin 4).succAbove 0 = 0 := by decide
  have u1 : (2 : Fin 4).succAbove 1 = 1 := by decide
  have u2 : (2 : Fin 4).succAbove 2 = 3 := by decide
  have v0 : (3 : Fin 4).succAbove 0 = 0 := by decide
  have v1 : (3 : Fin 4).succAbove 1 = 1 := by decide
  have v2 : (3 : Fin 4).succAbove 2 = 2 := by decide
  simp only [hpow0, hpow1, hpow2, hpow3, one_mul, neg_mul, submatrix_det3,
    s0, s1, s2, t0, t1, t2, u0, u1, u2, v0, v1, v2]
  try ring

lemma submatrix_det4 (A : Matrix (Fin 5) (Fin 5) ℤ) (j : Fin 5) :
    (A.submatrix Fin.succ j.succAbove).det =
      let B : Matrix (Fin 4) (Fin 4) ℤ := A.submatrix Fin.succ j.succAbove
      B 0 0 * det3 (B 1 1) (B 1 2) (B 1 3) (B 2 1) (B 2 2) (B 2 3) (B 3 1) (B 3 2) (B 3 3)
      - B 0 1 * det3 (B 1 0) (B 1 2) (B 1 3) (B 2 0) (B 2 2) (B 2 3) (B 3 0) (B 3 2) (B 3 3)
      + B 0 2 * det3 (B 1 0) (B 1 1) (B 1 3) (B 2 0) (B 2 1) (B 2 3) (B 3 0) (B 3 1) (B 3 3)
      - B 0 3 * det3 (B 1 0) (B 1 1) (B 1 2) (B 2 0) (B 2 1) (B 2 2) (B 3 0) (B 3 1) (B 3 2) := by
  simpa using (det4_eq (A.submatrix Fin.succ j.succAbove)).symm

lemma det5_eq (A : Matrix (Fin 5) (Fin 5) ℤ) :
    det5 (fun i j => A i j) = A.det := by
  unfold det5
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_five]
  have hpow0 : ((-1 : ℤ) ^ ((0 : Fin 5) : ℕ)) = 1 := by decide
  have hpow1 : ((-1 : ℤ) ^ ((1 : Fin 5) : ℕ)) = -1 := by decide
  have hpow2 : ((-1 : ℤ) ^ ((2 : Fin 5) : ℕ)) = 1 := by decide
  have hpow3 : ((-1 : ℤ) ^ ((3 : Fin 5) : ℕ)) = -1 := by decide
  have hpow4 : ((-1 : ℤ) ^ ((4 : Fin 5) : ℕ)) = 1 := by decide
  -- Identify each Laplace 4×4 block with `d4`.
  have block (j : Fin 5) :
      (A.submatrix Fin.succ j.succAbove).det =
        (fun r0 r1 r2 r3 c0 c1 c2 c3 =>
          let b (i k : Fin 4) : ℤ :=
            A (![r0, r1, r2, r3] i) (![c0, c1, c2, c3] k)
          b 0 0 * det3 (b 1 1) (b 1 2) (b 1 3) (b 2 1) (b 2 2) (b 2 3) (b 3 1) (b 3 2) (b 3 3)
          - b 0 1 * det3 (b 1 0) (b 1 2) (b 1 3) (b 2 0) (b 2 2) (b 2 3) (b 3 0) (b 3 2) (b 3 3)
          + b 0 2 * det3 (b 1 0) (b 1 1) (b 1 3) (b 2 0) (b 2 1) (b 2 3) (b 3 0) (b 3 1) (b 3 3)
          - b 0 3 * det3 (b 1 0) (b 1 1) (b 1 2) (b 2 0) (b 2 1) (b 2 2) (b 3 0) (b 3 1) (b 3 2))
          1 2 3 4 (j.succAbove 0) (j.succAbove 1) (j.succAbove 2) (j.succAbove 3) := by
    have hB := det4_eq (A.submatrix Fin.succ j.succAbove)
    have hs (k : Fin 4) : Fin.succ k = (![1, 2, 3, 4] : Fin 4 → Fin 5) k := by
      fin_cases k <;> decide
    have hj (k : Fin 4) :
        j.succAbove k = ![j.succAbove 0, j.succAbove 1, j.succAbove 2, j.succAbove 3] k := by
      fin_cases k <;> simp
    simp only [Matrix.submatrix_apply] at hB ⊢
    convert hB.symm using 1
  have v0 : ![(0 : Fin 5).succAbove 0, (0 : Fin 5).succAbove 1,
      (0 : Fin 5).succAbove 2, (0 : Fin 5).succAbove 3] = (![1, 2, 3, 4] : Fin 4 → Fin 5) := by
    ext i; fin_cases i <;> decide
  have v1 : ![(1 : Fin 5).succAbove 0, (1 : Fin 5).succAbove 1,
      (1 : Fin 5).succAbove 2, (1 : Fin 5).succAbove 3] = (![0, 2, 3, 4] : Fin 4 → Fin 5) := by
    ext i; fin_cases i <;> decide
  have v2 : ![(2 : Fin 5).succAbove 0, (2 : Fin 5).succAbove 1,
      (2 : Fin 5).succAbove 2, (2 : Fin 5).succAbove 3] = (![0, 1, 3, 4] : Fin 4 → Fin 5) := by
    ext i; fin_cases i <;> decide
  have v3 : ![(3 : Fin 5).succAbove 0, (3 : Fin 5).succAbove 1,
      (3 : Fin 5).succAbove 2, (3 : Fin 5).succAbove 3] = (![0, 1, 2, 4] : Fin 4 → Fin 5) := by
    ext i; fin_cases i <;> decide
  have v4 : ![(4 : Fin 5).succAbove 0, (4 : Fin 5).succAbove 1,
      (4 : Fin 5).succAbove 2, (4 : Fin 5).succAbove 3] = (![0, 1, 2, 3] : Fin 4 → Fin 5) := by
    ext i; fin_cases i <;> decide
  simp only [hpow0, hpow1, hpow2, hpow3, hpow4, one_mul, neg_mul, block, v0, v1, v2, v3, v4]
  ring

lemma eucl_inner (x y : EuclideanSpace ℝ (Fin 5)) :
    ⟪x, y⟫ = ∑ i : Fin 5, x i * y i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

lemma inner_q28A_coords (i : Fin 28) (x : EuclideanSpace ℝ (Fin 5)) :
    ⟪q28A i, x⟫ =
      (q28AZ i 0 : ℝ) * x 0 + (q28AZ i 1 : ℝ) * x 1 + (q28AZ i 2 : ℝ) * x 2 +
        (q28AZ i 3 : ℝ) * x 3 + (q28AZ i 4 : ℝ) * x 4 := by
  rw [eucl_inner]
  simp [q28A_int, Fin.sum_univ_five]

lemma orbitDen_pos (o : Fin 20) : (0 : ℤ) < orbitDen o := by
  fin_cases o <;> simp [orbitDen]

lemma orbitDen_ne_zero (o : Fin 20) : orbitDen o ≠ 0 :=
  (orbitDen_pos o).ne'

lemma signCoord_sq (s : Fin 16) (j : Fin 5) : signCoord s j * signCoord s j = 1 := by
  unfold signCoord
  split_ifs <;> simp

lemma signCoord_abs (s : Fin 16) (j : Fin 5) : |signCoord s j| = 1 := by
  unfold signCoord
  split_ifs <;> simp

lemma signCoord_last (s : Fin 16) : signCoord s 4 = 1 := by
  unfold signCoord
  simp

lemma xor_lt_16 (s t : Fin 16) : s.val.xor t.val < 16 := by
  have := Nat.xor_lt_two_pow (n := 4) (Nat.lt_of_lt_of_le s.isLt (by decide))
    (Nat.lt_of_lt_of_le t.isLt (by decide))
  simpa using this

def signXor (s t : Fin 16) : Fin 16 :=
  ⟨s.val.xor t.val, xor_lt_16 s t⟩

lemma orbitPoint_apply (o : Fin 20) (j : Fin 5) :
    orbitPoint o j = (orbitNum o j : ℝ) / (orbitDen o : ℝ) := by
  simp [orbitPoint, vec5_apply]
  fin_cases j <;> simp

lemma flipPoint_apply (s : Fin 16) (x : EuclideanSpace ℝ (Fin 5)) (j : Fin 5) :
    flipPoint s x j = (signCoord s j : ℝ) * x j := by
  simp [flipPoint, vec5_apply]
  fin_cases j <;> simp

lemma flipPoint_add (s : Fin 16) (x y : EuclideanSpace ℝ (Fin 5)) :
    flipPoint s (x + y) = flipPoint s x + flipPoint s y := by
  ext j
  simp [flipPoint_apply, eucl_add]
  ring

lemma flipPoint_smul (s : Fin 16) (c : ℝ) (x : EuclideanSpace ℝ (Fin 5)) :
    flipPoint s (c • x) = c • flipPoint s x := by
  ext j
  simp [flipPoint_apply, eucl_smul]
  ring

lemma flipPoint_neg (s : Fin 16) (x : EuclideanSpace ℝ (Fin 5)) :
    flipPoint s (-x) = - flipPoint s x := by
  simpa [neg_smul] using flipPoint_smul s (-1) x

lemma flipPoint_sub (s : Fin 16) (x y : EuclideanSpace ℝ (Fin 5)) :
    flipPoint s (x - y) = flipPoint s x - flipPoint s y := by
  simp [sub_eq_add_neg, flipPoint_add, flipPoint_neg]

lemma flipPoint_flipPoint (s : Fin 16) (x : EuclideanSpace ℝ (Fin 5)) :
    flipPoint s (flipPoint s x) = x := by
  ext j
  have hsq : (signCoord s j : ℝ) * (signCoord s j : ℝ) = 1 := by
    norm_cast
    exact_mod_cast signCoord_sq s j
  rw [flipPoint_apply, flipPoint_apply, ← mul_assoc, hsq, one_mul]

lemma flipPoint_inj (s : Fin 16) : Function.Injective (flipPoint s) := by
  intro x y h
  simpa [flipPoint_flipPoint] using congrArg (flipPoint s) h

lemma orbitPoint_U : orbitPoint 1 = q28U := by
  ext j
  simp [orbitPoint_apply, q28U, orbitNum, orbitDen]
  fin_cases j <;> simp [PiLp.single_apply]

lemma orbitPoint_V : orbitPoint 0 = q28V := by
  ext j
  simp [orbitPoint_apply, q28V, orbitNum, orbitDen]
  fin_cases j <;> simp [PiLp.single_apply]

lemma flipPoint_U (s : Fin 16) : flipPoint s q28U = q28U := by
  ext j
  simp [flipPoint_apply, q28U, PiLp.single_apply]
  split_ifs with h
  · simp [h, signCoord_last]
  · ring

theorem exists_rowImage :
    ∀ (s : Fin 16) (i : Fin 28), ∃ j : Fin 28,
      ∀ k : Fin 5, q28AZ j k = q28AZ i k * signCoord s k := by
  decide

noncomputable def rowImage (s : Fin 16) (i : Fin 28) : Fin 28 :=
  Classical.choose (exists_rowImage s i)

lemma rowImage_spec (s : Fin 16) (i : Fin 28) (k : Fin 5) :
    q28AZ (rowImage s i) k = q28AZ i k * signCoord s k :=
  Classical.choose_spec (exists_rowImage s i) k

lemma inner_flip (s : Fin 16) (i : Fin 28) (x : EuclideanSpace ℝ (Fin 5)) :
    ⟪q28A i, flipPoint s x⟫ = ⟪q28A (rowImage s i), x⟫ := by
  simp only [inner_q28A_coords, flipPoint_apply, rowImage_spec, Int.cast_mul]
  ring

lemma flipPoint_mem (s : Fin 16) {x : EuclideanSpace ℝ (Fin 5)}
    (hx : x ∈ Hpoly q28A q28B) : flipPoint s x ∈ Hpoly q28A q28B := by
  intro i
  simpa [q28B, inner_flip] using hx (rowImage s i)

lemma flipPoint_segment (s : Fin 16) (x y : EuclideanSpace ℝ (Fin 5)) :
    flipPoint s '' segment ℝ x y = segment ℝ (flipPoint s x) (flipPoint s y) := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp
    refine ⟨a, b, ha, hb, hab, ?_⟩
    simp [flipPoint_add, flipPoint_smul]
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨a • x + b • y, ⟨a, b, ha, hb, hab, rfl⟩, ?_⟩
    simp [flipPoint_add, flipPoint_smul]

lemma flipPoint_openSegment (s : Fin 16) (x y : EuclideanSpace ℝ (Fin 5)) :
    flipPoint s '' openSegment ℝ x y = openSegment ℝ (flipPoint s x) (flipPoint s y) := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp
    refine ⟨a, b, ha, hb, hab, ?_⟩
    simp [flipPoint_add, flipPoint_smul]
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨a • x + b • y, ⟨a, b, ha, hb, hab, rfl⟩, ?_⟩
    simp [flipPoint_add, flipPoint_smul]

lemma adj_flip (s : Fin 16) {x y : EuclideanSpace ℝ (Fin 5)}
    (h : Adj (Hpoly q28A q28B) x y) :
    Adj (Hpoly q28A q28B) (flipPoint s x) (flipPoint s y) := by
  refine ⟨fun heq => h.1 (flipPoint_inj s heq), ?_⟩
  constructor
  · intro z hz
    rw [← flipPoint_segment] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    exact flipPoint_mem s (h.2.1 hp)
  · intro p hp q hq z hzS hop
    have hp' : flipPoint s p ∈ Hpoly q28A q28B := flipPoint_mem s hp
    have hq' : flipPoint s q ∈ Hpoly q28A q28B := flipPoint_mem s hq
    have hz' : flipPoint s z ∈ segment ℝ x y := by
      have : z ∈ flipPoint s '' segment ℝ x y := by
        rw [flipPoint_segment]; exact hzS
      obtain ⟨w, hw, hzw⟩ := this
      simpa [← hzw, flipPoint_flipPoint] using hw
    have hop' : flipPoint s z ∈ openSegment ℝ (flipPoint s p) (flipPoint s q) := by
      rw [← flipPoint_openSegment]
      exact ⟨z, hop, rfl⟩
    have hmem := h.2.2 hp' hq' hz' hop'
    have : p ∈ flipPoint s '' segment ℝ x y :=
      ⟨flipPoint s p, hmem, by simp [flipPoint_flipPoint]⟩
    rwa [flipPoint_segment] at this

noncomputable def signOf (x : EuclideanSpace ℝ (Fin 5)) : Fin 16 :=
  ⟨(if x 0 < 0 then 1 else 0) +
    (if x 1 < 0 then 2 else 0) +
    (if x 2 < 0 then 4 else 0) +
    (if x 3 < 0 then 8 else 0), by
      have : (if x 0 < 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega
      have : (if x 1 < 0 then 2 else 0) ≤ 2 := by split_ifs <;> omega
      have : (if x 2 < 0 then 4 else 0) ≤ 4 := by split_ifs <;> omega
      have : (if x 3 < 0 then 8 else 0) ≤ 8 := by split_ifs <;> omega
      omega⟩

lemma signCoord_signOf (x : EuclideanSpace ℝ (Fin 5)) (j : Fin 4) :
    signCoord (signOf x) j.castSucc = if x j.castSucc < 0 then -1 else 1 := by
  fin_cases j <;> simp [signCoord, signOf] <;> split_ifs <;> omega

lemma flip_signOf_nonneg (x : EuclideanSpace ℝ (Fin 5)) (j : Fin 4) :
    0 ≤ flipPoint (signOf x) x j.castSucc := by
  have hsc := signCoord_signOf x j
  rw [flipPoint_apply, hsc]
  split_ifs with h
  · simp; nlinarith
  · simp; nlinarith [le_of_not_gt h]

lemma active_iff_intDotFlip (o : Fin 20) (s : Fin 16) (i : Fin 28) :
    ⟪q28A i, flipPoint s (orbitPoint o)⟫ = 1 ↔
      intDotFlip o s i = orbitDen o := by
  have hden : (orbitDen o : ℝ) ≠ 0 := Int.cast_ne_zero.2 (orbitDen_ne_zero o)
  have hpos : (0 : ℝ) < orbitDen o := Int.cast_pos.2 (orbitDen_pos o)
  have hinner :
      ⟪q28A i, flipPoint s (orbitPoint o)⟫ =
        (intDotFlip o s i : ℝ) / (orbitDen o : ℝ) := by
    unfold intDotFlip
    simp only [inner_q28A_coords, flipPoint_apply, orbitPoint_apply]
    field_simp [hden]
    norm_cast
  constructor
  · intro h
    have : (intDotFlip o s i : ℝ) / (orbitDen o : ℝ) = 1 := by simpa [hinner] using h
    have : (intDotFlip o s i : ℝ) = (orbitDen o : ℝ) := by
      field_simp [hden] at this
      linarith
    exact_mod_cast this
  · intro h
    simp [hinner, h, hden]

lemma signCoord_zero (j : Fin 5) : signCoord 0 j = 1 := by
  fin_cases j <;> simp [signCoord]

lemma flipPoint_zero (x : EuclideanSpace ℝ (Fin 5)) : flipPoint 0 x = x := by
  ext j
  simp [flipPoint_apply, signCoord_zero]

lemma flipPoint_V (s : Fin 16) : flipPoint s q28V = q28V := by
  ext j
  simp [flipPoint_apply, q28V, PiLp.single_apply]
  split_ifs with h
  · simp [h, signCoord_last]
  · ring

lemma signCoord_mul :
    ∀ (s t : Fin 16) (j : Fin 5),
      signCoord s j * signCoord t j = signCoord (signXor s t) j := by
  decide

lemma flipPoint_comp (s t : Fin 16) (x : EuclideanSpace ℝ (Fin 5)) :
    flipPoint s (flipPoint t x) = flipPoint (signXor s t) x := by
  ext j
  have h := signCoord_mul s t j
  simp [flipPoint_apply]
  have : (signCoord s j : ℝ) * (signCoord t j : ℝ) = (signCoord (signXor s t) j : ℝ) := by
    exact_mod_cast h
  linear_combination this * x j

lemma flipPoint_extreme (s : Fin 16) {x : EuclideanSpace ℝ (Fin 5)}
    (hx : x ∈ extremePoints ℝ (Hpoly q28A q28B)) :
    flipPoint s x ∈ extremePoints ℝ (Hpoly q28A q28B) := by
  refine ⟨flipPoint_mem s hx.1, ?_⟩
  intro p hp q hq hop
  have hop' : x ∈ openSegment ℝ (flipPoint s p) (flipPoint s q) := by
    have : flipPoint s x ∈ openSegment ℝ p q := hop
    have h := show flipPoint s (flipPoint s x) ∈
        openSegment ℝ (flipPoint s p) (flipPoint s q) by
      rw [← flipPoint_openSegment]
      exact ⟨flipPoint s x, this, rfl⟩
    simpa [flipPoint_flipPoint] using h
  have hfp : flipPoint s p = x :=
    hx.2 (flipPoint_mem s hp) (flipPoint_mem s hq) hop'
  have := congrArg (flipPoint s) hfp
  simpa [flipPoint_flipPoint] using this.symm.symm

lemma commonActive_dots (o1 o2 : Fin 20) (s : Fin 16) :
    (Finset.univ.filter (fun i : Fin 28 =>
      ⟪q28A i, orbitPoint o1⟫ = 1 ∧
        ⟪q28A i, flipPoint s (orbitPoint o2)⟫ = 1)) =
      (Finset.univ.filter (fun i : Fin 28 =>
        intDotFlip o1 0 i = orbitDen o1 ∧
          intDotFlip o2 s i = orbitDen o2)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨(active_iff_intDotFlip o1 0 i).1 (by simpa [flipPoint_zero] using h1),
      (active_iff_intDotFlip o2 s i).1 h2⟩
  · intro ⟨h1, h2⟩
    exact ⟨by simpa [flipPoint_zero] using (active_iff_intDotFlip o1 0 i).2 h1,
      (active_iff_intDotFlip o2 s i).2 h2⟩

noncomputable def chamberA (i : Fin 14) : EuclideanSpace ℝ (Fin 5) :=
  vec5 (chamberAZ i 0 : ℝ) (chamberAZ i 1 : ℝ) (chamberAZ i 2 : ℝ)
    (chamberAZ i 3 : ℝ) (chamberAZ i 4 : ℝ)

noncomputable def chamberB (i : Fin 14) : ℝ := (chamberBZ i : ℝ)

lemma chamberA_apply (i : Fin 14) (j : Fin 5) :
    chamberA i j = (chamberAZ i j : ℝ) := by
  simp [chamberA, vec5_apply]
  fin_cases j <;> simp

lemma inner_chamber (i : Fin 14) (x : EuclideanSpace ℝ (Fin 5)) :
    ⟪chamberA i, x⟫ =
      (chamberAZ i 0 : ℝ) * x 0 + (chamberAZ i 1 : ℝ) * x 1 +
        (chamberAZ i 2 : ℝ) * x 2 + (chamberAZ i 3 : ℝ) * x 3 +
          (chamberAZ i 4 : ℝ) * x 4 := by
  rw [eucl_inner]
  simp [chamberA_apply, Fin.sum_univ_five]

lemma chamber_of_nonneg {x : EuclideanSpace ℝ (Fin 5)}
    (hx : x ∈ Hpoly q28A q28B)
    (hnn : ∀ j : Fin 4, 0 ≤ x j.castSucc) :
    ∀ i : Fin 14, ⟪chamberA i, x⟫ ≤ chamberB i := by
  intro i
  have hx0 := hx 0
  have hx2 := hx 2
  have hx4 := hx 4
  have hx6 := hx 6
  have hx10 := hx 10
  have hx14 := hx 14
  have hx16 := hx 16
  have hx18 := hx 18
  have hx20 := hx 20
  have hx24 := hx 24
  simp [q28B, inner_q28A_coords, q28AZ] at hx0 hx2 hx4 hx6 hx10 hx14 hx16 hx18 hx20 hx24
  fin_cases i <;> simp [inner_chamber, chamberB, chamberAZ, chamberBZ]
  · linarith [hx0]
  · linarith [hx2]
  · linarith [hx4]
  · linarith [hx6]
  · linarith [hx10]
  · linarith [hx14]
  · linarith [hx16]
  · linarith [hx18]
  · linarith [hx20]
  · linarith [hx24]
  · have h := hnn (0 : Fin 4)
    have : (0 : Fin 4).castSucc = (0 : Fin 5) := rfl
    rw [this] at h; linarith
  · have h := hnn (1 : Fin 4)
    have : (1 : Fin 4).castSucc = (1 : Fin 5) := rfl
    rw [this] at h; linarith
  · have h := hnn (2 : Fin 4)
    have : (2 : Fin 4).castSucc = (2 : Fin 5) := rfl
    rw [this] at h; linarith
  · have h := hnn (3 : Fin 4)
    have : (3 : Fin 4).castSucc = (3 : Fin 5) := rfl
    rw [this] at h; linarith

lemma orig_of_chamber {x : EuclideanSpace ℝ (Fin 5)}
    (hch : ∀ i : Fin 14, ⟪chamberA i, x⟫ ≤ chamberB i) :
    x ∈ Hpoly q28A q28B := by
  have hn0 : 0 ≤ x 0 := by
    have h := hch 10
    simp [inner_chamber, chamberB, chamberAZ, chamberBZ] at h
    linarith
  have hn1 : 0 ≤ x 1 := by
    have h := hch 11
    simp [inner_chamber, chamberB, chamberAZ, chamberBZ] at h
    linarith
  have hn2 : 0 ≤ x 2 := by
    have h := hch 12
    simp [inner_chamber, chamberB, chamberAZ, chamberBZ] at h
    linarith
  have hn3 : 0 ≤ x 3 := by
    have h := hch 13
    simp [inner_chamber, chamberB, chamberAZ, chamberBZ] at h
    linarith
  have c0 := hch 0
  have c1 := hch 1
  have c2 := hch 2
  have c3 := hch 3
  have c4 := hch 4
  have c5 := hch 5
  have c6 := hch 6
  have c7 := hch 7
  have c8 := hch 8
  have c9 := hch 9
  simp [inner_chamber, chamberB, chamberAZ, chamberBZ] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
  intro i
  fin_cases i
  all_goals
    simp [q28B, inner_q28A_coords, q28AZ]
    nlinarith [hn0, hn1, hn2, hn3, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9]

lemma extreme_in_chamber {y : EuclideanSpace ℝ (Fin 5)}
    (hy : y ∈ extremePoints ℝ (Hpoly q28A q28B))
    (hnn : ∀ j : Fin 4, 0 ≤ y j.castSucc) :
    y ∈ extremePoints ℝ (Hpoly chamberA chamberB) := by
  have hch : y ∈ Hpoly chamberA chamberB := chamber_of_nonneg hy.1 hnn
  refine ⟨hch, ?_⟩
  intro p hp q hq hop
  exact hy.2 (orig_of_chamber hp) (orig_of_chamber hq) hop

lemma orbit_nums_inj :
    ∀ o1 o2 : Fin 20,
      (∀ j : Fin 5, orbitNum o1 j * orbitDen o2 = orbitNum o2 j * orbitDen o1) →
        o1 = o2 := by
  decide

lemma orbitPoint_inj : Function.Injective orbitPoint := by
  intro o1 o2 h
  apply orbit_nums_inj
  intro j
  have hj := congrArg (fun z : EuclideanSpace ℝ (Fin 5) => z j) h
  simp [orbitPoint_apply] at hj
  have hden1 : (orbitDen o1 : ℝ) ≠ 0 := Int.cast_ne_zero.2 (orbitDen_ne_zero o1)
  have hden2 : (orbitDen o2 : ℝ) ≠ 0 := Int.cast_ne_zero.2 (orbitDen_ne_zero o2)
  field_simp [hden1, hden2] at hj
  have : orbitNum o1 j * orbitDen o2 = orbitNum o2 j * orbitDen o1 := by
    exact_mod_cast (by linarith [hj] : (orbitNum o1 j * orbitDen o2 : ℝ) =
      (orbitNum o2 j * orbitDen o1 : ℝ))
  exact this

lemma orbitPoint_nonneg (o : Fin 20) (j : Fin 4) :
    0 ≤ orbitPoint o j.castSucc := by
  fin_cases o <;> fin_cases j <;> simp [orbitPoint_apply, orbitNum, orbitDen] <;> norm_num

lemma order_five (t : Finset (Fin 14)) (hc : t.card = 5) :
    ∃ s0 s1 s2 s3 s4 : Fin 14,
      s0 < s1 ∧ s1 < s2 ∧ s2 < s3 ∧ s3 < s4 ∧ t = {s0, s1, s2, s3, s4} := by
  have hne : t.Nonempty := Finset.card_pos.mp (by omega)
  let s0 := t.min' hne
  have hs0 : s0 ∈ t := t.min'_mem hne
  let t1 := t.erase s0
  have hc1 : t1.card = 4 := by simp [t1, Finset.card_erase_of_mem hs0, hc]
  have hne1 : t1.Nonempty := Finset.card_pos.mp (by omega)
  let s1 := t1.min' hne1
  have hs1 : s1 ∈ t1 := t1.min'_mem hne1
  have hs1t : s1 ∈ t := Finset.mem_of_mem_erase hs1
  have hs01 : s0 < s1 :=
    lt_of_le_of_ne (t.min'_le s1 hs1t) (Ne.symm (Finset.ne_of_mem_erase hs1))
  let t2 := t1.erase s1
  have hc2 : t2.card = 3 := by simp [t2, Finset.card_erase_of_mem hs1, hc1]
  have hne2 : t2.Nonempty := Finset.card_pos.mp (by omega)
  let s2 := t2.min' hne2
  have hs2 : s2 ∈ t2 := t2.min'_mem hne2
  have hs2t : s2 ∈ t := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hs2)
  have hs12 : s1 < s2 :=
    lt_of_le_of_ne (t1.min'_le s2 (Finset.mem_of_mem_erase hs2))
      (Ne.symm (Finset.ne_of_mem_erase hs2))
  let t3 := t2.erase s2
  have hc3 : t3.card = 2 := by simp [t3, Finset.card_erase_of_mem hs2, hc2]
  have hne3 : t3.Nonempty := Finset.card_pos.mp (by omega)
  let s3 := t3.min' hne3
  have hs3 : s3 ∈ t3 := t3.min'_mem hne3
  have hs3t : s3 ∈ t :=
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hs3))
  have hs23 : s2 < s3 :=
    lt_of_le_of_ne (t2.min'_le s3 (Finset.mem_of_mem_erase hs3))
      (Ne.symm (Finset.ne_of_mem_erase hs3))
  let t4 := t3.erase s3
  have hc4 : t4.card = 1 := by simp [t4, Finset.card_erase_of_mem hs3, hc3]
  have hne4 : t4.Nonempty := Finset.card_pos.mp (by omega)
  let s4 := t4.min' hne4
  have hs4 : s4 ∈ t4 := t4.min'_mem hne4
  have hs4t : s4 ∈ t :=
    Finset.mem_of_mem_erase
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hs4)))
  have hs34 : s3 < s4 :=
    lt_of_le_of_ne (t3.min'_le s4 (Finset.mem_of_mem_erase hs4))
      (Ne.symm (Finset.ne_of_mem_erase hs4))
  have hsub : ({s0, s1, s2, s3, s4} : Finset (Fin 14)) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h | h <;> subst h <;>
      first | exact hs0 | exact hs1t | exact hs2t | exact hs3t | exact hs4t
  have hne01 : s0 ≠ s1 := hs01.ne
  have hne02 : s0 ≠ s2 := (hs01.trans hs12).ne
  have hne03 : s0 ≠ s3 := (hs01.trans (hs12.trans hs23)).ne
  have hne04 : s0 ≠ s4 := (hs01.trans (hs12.trans (hs23.trans hs34))).ne
  have hne12 : s1 ≠ s2 := hs12.ne
  have hne13 : s1 ≠ s3 := (hs12.trans hs23).ne
  have hne14 : s1 ≠ s4 := (hs12.trans (hs23.trans hs34)).ne
  have hne23 : s2 ≠ s3 := hs23.ne
  have hne24 : s2 ≠ s4 := (hs23.trans hs34).ne
  have hne34 : s3 ≠ s4 := hs34.ne
  have hcard : ({s0, s1, s2, s3, s4} : Finset (Fin 14)).card = 5 := by
    simp [Finset.card_insert_of_notMem, hne01, hne02, hne03, hne04, hne12, hne13, hne14,
      hne23, hne24, hne34]
  refine ⟨s0, s1, s2, s3, s4, hs01, hs12, hs23, hs34, ?_⟩
  exact (Finset.eq_of_subset_of_card_le hsub (by simp [hc, hcard])).symm

lemma active_chamber_span_eq_top {y : EuclideanSpace ℝ (Fin 5)}
    (hy : y ∈ extremePoints ℝ (Hpoly chamberA chamberB)) :
    Submodule.span ℝ
      (chamberA '' ((Finset.univ.filter
        (fun i : Fin 14 => ⟪chamberA i, y⟫ = chamberB i) : Set _))) = ⊤ := by
  let sAct := Finset.univ.filter (fun i : Fin 14 => ⟪chamberA i, y⟫ = chamberB i)
  let W := Submodule.span ℝ (chamberA '' (sAct : Set _))
  have horth : W.orthogonal = ⊥ := by
    apply eq_bot_iff.2
    intro z hz
    have hz' : ∀ i ∈ sAct, ⟪chamberA i, z⟫ = 0 := by
      intro i hi
      have hv : chamberA i ∈ W :=
        Submodule.subset_span (Set.mem_image_of_mem chamberA hi)
      have horth := (Submodule.mem_orthogonal W z).1 hz
      simpa [real_inner_comm] using horth (chamberA i) hv
    exact extreme_tight_orthogonal hy (fun i ht =>
      hz' i (Finset.mem_filter.2 ⟨Finset.mem_univ i, ht⟩))
  haveI : CompleteSpace W := FiniteDimensional.complete ℝ W
  have hW : W.orthogonal.orthogonal = W := Submodule.orthogonal_orthogonal W
  have : W = ⊤ := by
    have : W.orthogonal.orthogonal = ⊤ := by simp [horth]
    simpa [hW] using this
  exact this

lemma cramer_coords (A : Matrix (Fin 5) (Fin 5) ℝ) (y b : Fin 5 → ℝ)
    (hAy : A *ᵥ y = b) (hdet : A.det ≠ 0) (j : Fin 5) :
    y j = (A.updateCol j b).det / A.det := by
  have hcr : A *ᵥ cramer A b = A.det • b := mulVec_cramer A b
  have h0 : A *ᵥ (cramer A b - A.det • y) = 0 := by
    calc
      A *ᵥ (cramer A b - A.det • y)
          = A *ᵥ cramer A b - A *ᵥ (A.det • y) := mulVec_sub _ _ _
      _ = A.det • b - A.det • (A *ᵥ y) := by rw [hcr, mulVec_smul]
      _ = A.det • b - A.det • b := by rw [hAy]
      _ = 0 := sub_self _
  have hzero : cramer A b - A.det • y = 0 := by
    have := congrArg (fun v => A.adjugate *ᵥ v) h0
    have hmul : A.det • (cramer A b - A.det • y) = 0 := by
      have hassoc :
          A.adjugate *ᵥ (A *ᵥ (cramer A b - A.det • y)) =
            (A.adjugate * A) *ᵥ (cramer A b - A.det • y) :=
        mulVec_mulVec (cramer A b - A.det • y) A.adjugate A
      have : (A.adjugate * A) *ᵥ (cramer A b - A.det • y) = 0 := by
        rw [← hassoc]; simp [h0]
      rw [adjugate_mul, smul_mulVec, one_mulVec] at this
      exact this
    exact (smul_eq_zero.1 hmul).resolve_left hdet
  have heq : cramer A b = A.det • y := sub_eq_zero.1 hzero
  have hj : (A.updateCol j b).det = A.det * y j := by
    have := congrArg (fun v => v j) heq
    simpa [cramer_apply, Pi.smul_apply, smul_eq_mul] using this
  field_simp [hdet]
  linarith [hj]

lemma replaceCol_updateCol (M : Matrix (Fin 5) (Fin 5) ℤ) (j : Fin 5) (b : Fin 5 → ℤ) :
    Matrix.of (replaceCol (fun i k => M i k) j b) = M.updateCol j b := by
  ext i k
  simp [replaceCol, Matrix.updateCol, Matrix.of_apply, Function.update]

def coord_proj :
    EuclideanSpace ℝ (Fin 5) →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun := fun x j => x j
  map_add' := by intros; funext; rfl
  map_smul' := by intros; funext; rfl

lemma coord_proj_inj : Function.Injective coord_proj := by
  intro x y h
  refine PiLp.ext ?_
  intro j
  exact congrFun h j

lemma rowDotN_eq (s : Fin 14) (v : Fin 5 → ℤ) :
    rowDotN s.val (v 0) (v 1) (v 2) (v 3) (v 4) = intDot5 (chamberAZ s) v := by
  fin_cases s <;> simp [rowDotN, intDot5, chamberAZ] <;> ring

lemma bZ_eq (s : Fin 14) : bZ s.val = chamberBZ s := by
  fin_cases s <;> simp [bZ, chamberBZ]

lemma band_left {a b : Bool} (h : Bool.and a b = true) : a = true := by
  cases a
  · cases h
  · rfl

lemma band_right {a b : Bool} (h : Bool.and a b = true) : b = true := by
  cases a
  · cases h
  · exact h

lemma list_getD_lt_of_all {l : List ℕ} {i d b : ℕ}
    (h : ∀ x ∈ l, x < b) (hd : d < b) : l.getD i d < b := by
  cases hopt : l[i]? with
  | none =>
      simp [List.getD, hopt]
      exact hd
  | some x =>
      simp [List.getD, hopt]
      exact h x (List.mem_of_getElem? hopt)

lemma failRowChunks_lt :
    (List.range 63).all
      (fun c => (failRowAtChunk c).all (fun x => decide (x < 14))) = true :=
  rfl

lemma failRowAtChunk_all_lt {c : ℕ} (hc : c < 63) :
    (failRowAtChunk c).all (fun x => decide (x < 14)) = true := by
  have h := failRowChunks_lt
  have : c ∈ List.range 63 := List.mem_range.mpr hc
  exact (List.all_eq_true.mp h) c this

lemma failRowAt_lt {n : ℕ} (hn : n < 2002) : failRowAt n < 14 := by
  have hc : n / 32 < 63 := by omega
  unfold failRowAt
  refine list_getD_lt_of_all ?_ (by decide)
  intro x hx
  exact of_decide_eq_true
    ((List.all_eq_true.mp (failRowAtChunk_all_lt hc)) x hx)

lemma range_eq_Iio_nat (n : ℕ) : Finset.range n = Finset.Iio n := by
  ext x
  simp [Finset.mem_range, Finset.mem_Iio]

lemma origCount_eq_count (v : Fin 5 → ℤ) (d : ℤ) :
    origCount v d =
      Nat.count (fun n => intDot5 (q28AZ (of28 n)) v = d) 28 := by
  repeat rw [Nat.count_succ]
  rw [Nat.count_zero]
  simp [origCount, of28]
  rfl

lemma origCount_eq_filter (v : Fin 5 → ℤ) (d : ℤ) :
    origCount v d =
      (Finset.univ.filter (fun i : Fin 28 => intDot5 (q28AZ i) v = d)).card := by
  rw [origCount_eq_count, Nat.count_eq_card_filter_range, range_eq_Iio_nat,
    ← Fin.map_valEmbedding_univ, Finset.filter_map]
  simp [Finset.card_map, of28, Fin.valEmbedding_apply, Nat.mod_eq_of_lt]

lemma extreme_nonneg_orbit {y : EuclideanSpace ℝ (Fin 5)}
    (hy : y ∈ extremePoints ℝ (Hpoly q28A q28B))
    (hnn : ∀ j : Fin 4, 0 ≤ y j.castSucc) :
    ∃ o : Fin 20, y = orbitPoint o := by
  have hyCh := extreme_in_chamber hy hnn
  let sAct := Finset.univ.filter (fun i : Fin 14 => ⟪chamberA i, y⟫ = chamberB i)
  let W := Submodule.span ℝ (chamberA '' (sAct : Set _))
  have htop : W = ⊤ := active_chamber_span_eq_top hyCh
  have hrank : Module.finrank ℝ W = 5 := by
    rw [htop]
    exact (finrank_top (R := ℝ) (M := EuclideanSpace ℝ (Fin 5))).trans
      (finrank_euclideanSpace_fin (𝕜 := ℝ))
  obtain ⟨g0, hgmem, hgspan, hgindep⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (K := ℝ)
      (s := (chamberA '' (sAct : Set _)))
  let e : Fin (Module.finrank ℝ W) ≃ Fin 5 := finCongr hrank
  let g : Fin 5 → EuclideanSpace ℝ (Fin 5) := g0 ∘ e.symm
  have hgmem' (i : Fin 5) : g i ∈ (chamberA '' (sAct : Set _)) := hgmem _
  have hgindep' : LinearIndependent ℝ g := hgindep.comp _ e.symm.injective
  have hσex (i : Fin 5) : ∃ k ∈ sAct, chamberA k = g i := by
    simpa [Set.mem_image] using hgmem' i
  let σ : Fin 5 → Fin 14 := fun i => Classical.choose (hσex i)
  have hσsAct (i : Fin 5) : σ i ∈ sAct := (Classical.choose_spec (hσex i)).1
  have hσg (i : Fin 5) : chamberA (σ i) = g i := (Classical.choose_spec (hσex i)).2
  have hσinj : Function.Injective σ := by
    intro i k hik
    exact hgindep'.injective (by rw [← hσg i, ← hσg k, hik])
  let t : Finset (Fin 14) := Finset.univ.image σ
  have htcard : t.card = 5 := by
    rw [Finset.card_image_of_injective _ hσinj]; simp
  obtain ⟨s0, s1, s2, s3, s4, hs01, hs12, hs23, hs34, ht⟩ := order_five t htcard
  have hsAct (s : Fin 14) (hs : s ∈ t) : s ∈ sAct := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hs
    exact hσsAct i
  have hrange :
      Set.range (fun i : Fin 5 => chamberA (![s0, s1, s2, s3, s4] i)) = Set.range g := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      have : ![s0, s1, s2, s3, s4] i ∈ t := by
        rw [ht]; fin_cases i <;> simp
      obtain ⟨k, _, hk⟩ := Finset.mem_image.1 this
      exact ⟨k, by rw [← hσg k, hk]⟩
    · rintro ⟨k, rfl⟩
      have : σ k ∈ t := Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩
      have : σ k ∈ ({s0, s1, s2, s3, s4} : Finset (Fin 14)) := by simpa [ht] using this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h | h | h
      · exact ⟨0, by simp [← h, hσg]⟩
      · exact ⟨1, by simp [← h, hσg]⟩
      · exact ⟨2, by simp [← h, hσg]⟩
      · exact ⟨3, by simp [← h, hσg]⟩
      · exact ⟨4, by simp [← h, hσg]⟩
  have hspan_ord :
      Submodule.span ℝ
        (Set.range (fun i : Fin 5 => chamberA (![s0, s1, s2, s3, s4] i))) = ⊤ := by
    have hrange0 : Set.range g = Set.range g0 := by
      ext v
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨e.symm i, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨e i, by simp [g]⟩
    calc
      _ = Submodule.span ℝ (Set.range g) := by rw [hrange]
      _ = Submodule.span ℝ (Set.range g0) := by rw [hrange0]
      _ = W := hgspan
      _ = ⊤ := htop
  have hvec : LinearIndependent ℝ
      (fun i : Fin 5 => chamberA (![s0, s1, s2, s3, s4] i)) := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    have : Set.finrank ℝ
        (Set.range (fun i : Fin 5 => chamberA (![s0, s1, s2, s3, s4] i))) = 5 := by
      rw [Set.finrank, hspan_ord]
      exact (finrank_top (R := ℝ) (M := EuclideanSpace ℝ (Fin 5))).trans
        (finrank_euclideanSpace_fin (𝕜 := ℝ))
    simpa [this]
  have hrows : LinearIndependent ℝ
      (fun i : Fin 5 => (fun j => chamberA (![s0, s1, s2, s3, s4] i) j : Fin 5 → ℝ)) :=
    hvec.map' coord_proj (LinearMap.ker_eq_bot.2 coord_proj_inj)
  let AM : Matrix (Fin 5) (Fin 5) ℝ :=
    Matrix.of (fun i j => chamberA (![s0, s1, s2, s3, s4] i) j)
  have hdetR : AM.det ≠ 0 := by
    intro h0
    have hT : AMᵀ.det = 0 := by simpa [Matrix.det_transpose] using h0
    obtain ⟨v, hv0, hv⟩ := (exists_mulVec_eq_zero_iff (M := AMᵀ)).mpr hT
    have hsum : ∑ i, v i • AM i = 0 := by
      ext j
      have := congrArg (fun z => z j) hv
      simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_five] at this ⊢
      simp [AM, Matrix.of_apply] at this ⊢
      linarith
    have : v = 0 := funext <|
      Fintype.linearIndependent_iff.1 (by simpa [AM, Matrix.of_apply] using hrows) v
        (by simpa [AM, Matrix.of_apply] using hsum)
    exact hv0 this
  let MZ : Matrix (Fin 5) (Fin 5) ℤ := Matrix.of (matOf s0 s1 s2 s3 s4)
  have hAMmap : AM = MZ.map (Int.cast : ℤ → ℝ) := by
    ext i j
    simp [AM, MZ, matOf, chamberA_apply, Matrix.of_apply, Matrix.map]
  have hdetZ : MZ.det ≠ 0 := by
    have hmap : (MZ.map (Int.castRingHom ℝ)).det ≠ 0 := by
      simpa [hAMmap, Matrix.map] using hdetR
    have hrd := (RingHom.map_det (Int.castRingHom ℝ) MZ).symm
    have hmap' : (MZ.det : ℝ) ≠ 0 := by
      have : MZ.map (Int.castRingHom ℝ) = (Int.castRingHom ℝ).mapMatrix MZ := rfl
      rw [this] at hmap
      rwa [hrd] at hmap
    exact Int.cast_ne_zero.1 hmap'
  have hdet5 : det5 (matOf s0 s1 s2 s3 s4) ≠ 0 := by
    have h := det5_eq MZ
    have : (fun i j => MZ i j) = matOf s0 s1 s2 s3 s4 := by
      ext i j; simp [MZ, Matrix.of_apply]
    simpa [this] using h.trans_ne hdetZ
  let nums := cramerNums s0 s1 s2 s3 s4
  let d := det5 (matOf s0 s1 s2 s3 s4)
  let rhsZ : Fin 5 → ℤ := fun i => chamberBZ (![s0, s1, s2, s3, s4] i)
  let rhsR : Fin 5 → ℝ := fun i => chamberB (![s0, s1, s2, s3, s4] i)
  have hAy : AM *ᵥ (fun j => y j) = rhsR := by
    ext i
    have hs : ![s0, s1, s2, s3, s4] i ∈ t := by
      rw [ht]; fin_cases i <;> simp
    have hact := (Finset.mem_filter.1 (hsAct _ hs)).2
    have hinter := inner_chamber (![s0, s1, s2, s3, s4] i) y
    have hsum : ⟪chamberA (![s0, s1, s2, s3, s4] i), y⟫ =
        ∑ x, chamberA (![s0, s1, s2, s3, s4] i) x * y x := eucl_inner _ _
    simpa [Matrix.mulVec, dotProduct, AM, Matrix.of_apply, rhsR, hsum] using hact
  have hyCramer (j : Fin 5) :
      y j = (AM.updateCol j rhsR).det / AM.det :=
    cramer_coords AM (fun j => y j) rhsR hAy hdetR j
  have hdetmap : AM.det = (MZ.det : ℝ) := by
    simpa [hAMmap] using (RingHom.map_det (Int.castRingHom ℝ) MZ).symm
  have hdet5eq : (MZ.det : ℝ) = (d : ℝ) := by
    have h := det5_eq MZ
    have : (fun i j => MZ i j) = matOf s0 s1 s2 s3 s4 := by
      ext i j; simp [MZ, Matrix.of_apply]
    simp [d, this] at h
    simpa [MZ, Matrix.of_apply, this] using h.symm
  have hnums (j : Fin 5) : (AM.updateCol j rhsR).det = (nums j : ℝ) := by
    have : AM.updateCol j rhsR = (MZ.updateCol j rhsZ).map (Int.cast : ℤ → ℝ) := by
      ext a b
      by_cases hb : b = j
      · simp [AM, rhsR, rhsZ, hAMmap, hb, Matrix.updateCol, chamberB, Matrix.map]
      · simp [AM, rhsR, rhsZ, hAMmap, hb, Matrix.updateCol, Matrix.map]
    have hrd := RingHom.map_det (Int.castRingHom ℝ) (MZ.updateCol j rhsZ)
    have h5 : det5 (replaceCol (matOf s0 s1 s2 s3 s4) j rhsZ) =
        (MZ.updateCol j rhsZ).det := by
      have h := det5_eq (MZ.updateCol j rhsZ)
      have heq : (fun i k => (MZ.updateCol j rhsZ) i k) =
          replaceCol (matOf s0 s1 s2 s3 s4) j rhsZ := by
        ext i k
        simp [MZ, Matrix.of_apply, Matrix.updateCol, replaceCol, matOf, Function.update]
      simpa [heq] using h
    have hmapdet : ((MZ.updateCol j rhsZ).map (Int.cast : ℤ → ℝ)).det =
        ((Int.castRingHom ℝ).mapMatrix (MZ.updateCol j rhsZ)).det := rfl
    calc
      (AM.updateCol j rhsR).det
          = ((MZ.updateCol j rhsZ).map (Int.cast : ℤ → ℝ)).det := by rw [this]
      _ = ((Int.castRingHom ℝ).mapMatrix (MZ.updateCol j rhsZ)).det := hmapdet
      _ = ((MZ.updateCol j rhsZ).det : ℝ) := hrd.symm
      _ = (det5 (replaceCol (matOf s0 s1 s2 s3 s4) j rhsZ) : ℝ) := by rw [h5]
      _ = (nums j : ℝ) := rfl
  have hy_eq (j : Fin 5) : y j = (nums j : ℝ) / (d : ℝ) := by
    rw [hyCramer, hnums, hdetmap, hdet5eq]
  have hdR : (d : ℝ) ≠ 0 := Int.cast_ne_zero.2 hdet5
  have hfeas : feasibleNums nums d = true := by
    unfold feasibleNums
    refine decide_eq_true ?_
    intro i
    have hyi : ⟪chamberA i, y⟫ ≤ chamberB i := hyCh.1 i
    have hinter : ⟪chamberA i, y⟫ = (intDot5 (chamberAZ i) nums : ℝ) / (d : ℝ) := by
      simp [inner_chamber, hy_eq, intDot5, Fin.sum_univ_five]
      field_simp [hdR]
    rw [hinter] at hyi
    by_cases hdpos : (0 : ℤ) < d
    · have : (intDot5 (chamberAZ i) nums : ℝ) ≤ (chamberBZ i * d : ℝ) := by
        have := (div_le_iff₀ (Int.cast_pos.2 hdpos)).1 (by simpa [chamberB] using hyi)
        simpa [mul_comm] using this
      simp [hdpos]
      exact_mod_cast this
    · have hdneg : d < 0 :=
        lt_of_le_of_ne (le_of_not_gt hdpos) (show d ≠ 0 from hdet5)
      have : (chamberBZ i * d : ℝ) ≤ (intDot5 (chamberAZ i) nums : ℝ) := by
        have := (div_le_iff_of_neg (Int.cast_lt_zero.2 hdneg)).1
          (by simpa [chamberB] using hyi)
        simpa [mul_comm] using this
      simp [hdpos]
      exact_mod_cast this
  have hge : 5 ≤ origActiveCount nums d := by
    have hcard := spindle_tight_card hy
    have hceq : origActiveCount nums d =
        (Finset.univ.filter (fun i : Fin 28 => ⟪q28A i, y⟫ = 1)).card := by
      unfold origActiveCount
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hinter : ⟪q28A i, y⟫ = (intDot5 (q28AZ i) nums : ℝ) / (d : ℝ) := by
        simp [inner_q28A_coords, hy_eq, intDot5, Fin.sum_univ_five]
        field_simp [hdR]
      constructor
      · intro hdot
        simp [hinter, hdot, hdR]
      · intro htight
        have : (intDot5 (q28AZ i) nums : ℝ) / (d : ℝ) = 1 := by
          simpa [hinter] using htight
        have : (intDot5 (q28AZ i) nums : ℝ) = (d : ℝ) := by
          field_simp [hdR] at this
          linarith
        exact_mod_cast this
    simpa [hceq, q28B] using hcard
  let r := combRank s0.val s1.val s2.val s3.val s4.val
  have hr : r < 2002 :=
    combRank_lt s0.val s1.val s2.val s3.val s4.val hs01 hs12 hs23 hs34 s4.isLt
  have hok : certOkUnrank r = true := certOkUnrank_all r hr
  have hun : unrank5 r = (s0.val, s1.val, s2.val, s3.val, s4.val) :=
    unrank_rank s0.val s1.val s2.val s3.val s4.val hs01 hs12 hs23 hs34 s4.isLt
  let v : Fin 5 → ℤ := fun j => vecAt (5 * r + j.val)
  let dc := dAt r
  have hMv (hd : ∀ i : Fin 5,
      rowDotN (![s0, s1, s2, s3, s4] i).val (v 0) (v 1) (v 2) (v 3) (v 4) =
        dc * bZ (![s0, s1, s2, s3, s4] i).val) :
      MZ *ᵥ v = dc • rhsZ := by
    ext i
    have := hd i
    simp [Matrix.mulVec, dotProduct, MZ, Matrix.of_apply, matOf, Pi.smul_apply,
      smul_eq_mul, rhsZ, intDot5, bZ_eq, Fin.sum_univ_five] at this ⊢
    simpa [rowDotN_eq] using this
  have hMv0 (hd : ∀ i : Fin 5,
      rowDotN (![s0, s1, s2, s3, s4] i).val (v 0) (v 1) (v 2) (v 3) (v 4) = 0) :
      MZ *ᵥ v = 0 := by
    ext i
    have := hd i
    simp [Matrix.mulVec, dotProduct, MZ, Matrix.of_apply, matOf, intDot5,
      Fin.sum_univ_five] at this ⊢
    simpa [rowDotN_eq] using this
  have hy_of_int (hdc : dc ≠ 0)
      (hd : ∀ i : Fin 5,
        rowDotN (![s0, s1, s2, s3, s4] i).val (v 0) (v 1) (v 2) (v 3) (v 4) =
          dc * bZ (![s0, s1, s2, s3, s4] i).val) :
      ∀ j, y j = (v j : ℝ) / (dc : ℝ) := by
    have hZ := hMv hd
    have hdcR : (dc : ℝ) ≠ 0 := Int.cast_ne_zero.2 hdc
    have hmap : AM *ᵥ (fun j => (v j : ℝ)) = (dc : ℝ) • rhsR := by
      ext i
      have hZi := congrFun hZ i
      have hAMi : AM i = fun j => (MZ i j : ℝ) := by
        funext j; simp [hAMmap, Matrix.map_apply]
      simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hAMi,
        rhsR, rhsZ, chamberB] at hZi ⊢
      exact_mod_cast hZi
    have hAM : AM *ᵥ (fun j => (v j : ℝ) / (dc : ℝ)) = rhsR := by
      ext i
      have hi := congrFun hmap i
      simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi ⊢
      have hsum :
          ∑ x, AM i x * ((v x : ℝ) / (dc : ℝ)) =
            (∑ x, AM i x * (v x : ℝ)) / (dc : ℝ) := by
        simp_rw [div_eq_mul_inv, ← mul_assoc]
        rw [← Finset.sum_mul]
      rw [hsum, hi, mul_comm (dc : ℝ), mul_div_cancel_right₀ _ hdcR]
    have hAMunit : IsUnit AM :=
      (isUnit_iff_isUnit_det (A := AM)).mpr (isUnit_iff_ne_zero.mpr hdetR)
    have hv :
        (fun j => (v j : ℝ) / (dc : ℝ)) = fun j => y j :=
      (mulVec_injective_iff_isUnit (A := AM)).mpr hAMunit (hAM.trans hAy.symm)
    intro j
    simpa using (congrFun hv j).symm
  cases ht0 : (tagAt r == 0) with
  | true =>
    unfold certOkUnrank at hok
    simp only [hun] at hok
    rw [if_pos ht0] at hok
    have hvnB := band_right hok
    have hrows := band_left hok
    have hr4B := band_right hrows
    have hrows3 := band_left hrows
    have hr3B := band_right hrows3
    have hrows2 := band_left hrows3
    have hr2B := band_right hrows2
    have hrows1 := band_left hrows2
    have hr1B := band_right hrows1
    have hr0B := band_left hrows1
    have hr0 : rowDotN s0.val (v 0) (v 1) (v 2) (v 3) (v 4) = 0 :=
      beq_iff_eq.mp (by simpa [v] using hr0B)
    have hr1 : rowDotN s1.val (v 0) (v 1) (v 2) (v 3) (v 4) = 0 :=
      beq_iff_eq.mp (by simpa [v] using hr1B)
    have hr2 : rowDotN s2.val (v 0) (v 1) (v 2) (v 3) (v 4) = 0 :=
      beq_iff_eq.mp (by simpa [v] using hr2B)
    have hr3 : rowDotN s3.val (v 0) (v 1) (v 2) (v 3) (v 4) = 0 :=
      beq_iff_eq.mp (by simpa [v] using hr3B)
    have hr4 : rowDotN s4.val (v 0) (v 1) (v 2) (v 3) (v 4) = 0 :=
      beq_iff_eq.mp (by simpa [v] using hr4B)
    have hvn' :
        ((((v 0 ≠ 0 ∨ v 1 ≠ 0) ∨ v 2 ≠ 0) ∨ v 3 ≠ 0) ∨ v 4 ≠ 0) := by
      simpa [v, Bool.or_eq_true, bne_iff_ne] using hvnB
    have hd0 : ∀ i : Fin 5,
        rowDotN (![s0, s1, s2, s3, s4] i).val (v 0) (v 1) (v 2) (v 3) (v 4) = 0 := by
      intro i; fin_cases i
      · exact hr0
      · exact hr1
      · exact hr2
      · exact hr3
      · exact hr4
    have hZ := hMv0 hd0
    have hvR : (fun j => (v j : ℝ)) ≠ 0 := by
      intro hvzR
      have hv0 : v = 0 := by
        ext j
        have hj := congrFun hvzR j
        simp at hj
        exact Int.cast_eq_zero.mp hj
      have :
          ((((v 0 ≠ 0 ∨ v 1 ≠ 0) ∨ v 2 ≠ 0) ∨ v 3 ≠ 0) ∨ v 4 ≠ 0) := hvn'
      simp [hv0] at this
    have hAM0 : AM *ᵥ (fun j => (v j : ℝ)) = 0 := by
      ext i
      have hZi := congrFun hZ i
      have hAMi : AM i = fun j => (MZ i j : ℝ) := by
        funext j; simp [hAMmap, Matrix.map_apply]
      simp [Matrix.mulVec, dotProduct, hAMi] at hZi ⊢
      exact_mod_cast hZi
    have hnotUnit : ¬ IsUnit AM := by
      intro hU
      have hinj := (mulVec_injective_iff_isUnit (A := AM)).mpr hU
      have : (fun j => (v j : ℝ)) = 0 := hinj (by simp [hAM0])
      exact hvR this
    exact False.elim
      ((isUnit_iff_ne_zero.not.mp
        ((isUnit_iff_isUnit_det (A := AM)).not.mp hnotUnit)) hdetR)
  | false =>
    unfold certOkUnrank at hok
    simp only [hun] at hok
    rw [if_neg (Bool.eq_false_iff.mp ht0)] at hok
    have htag := band_right hok
    have hrowsd := band_left hok
    have hdcB := band_right hrowsd
    have hrows := band_left hrowsd
    have hr4B := band_right hrows
    have hrows3 := band_left hrows
    have hr3B := band_right hrows3
    have hrows2 := band_left hrows3
    have hr2B := band_right hrows2
    have hrows1 := band_left hrows2
    have hr1B := band_right hrows1
    have hr0B := band_left hrows1
    have hr0 : rowDotN s0.val (v 0) (v 1) (v 2) (v 3) (v 4) =
        dc * bZ s0.val := beq_iff_eq.mp (by simpa [v, dc] using hr0B)
    have hr1 : rowDotN s1.val (v 0) (v 1) (v 2) (v 3) (v 4) =
        dc * bZ s1.val := beq_iff_eq.mp (by simpa [v, dc] using hr1B)
    have hr2 : rowDotN s2.val (v 0) (v 1) (v 2) (v 3) (v 4) =
        dc * bZ s2.val := beq_iff_eq.mp (by simpa [v, dc] using hr2B)
    have hr3 : rowDotN s3.val (v 0) (v 1) (v 2) (v 3) (v 4) =
        dc * bZ s3.val := beq_iff_eq.mp (by simpa [v, dc] using hr3B)
    have hr4 : rowDotN s4.val (v 0) (v 1) (v 2) (v 3) (v 4) =
        dc * bZ s4.val := beq_iff_eq.mp (by simpa [v, dc] using hr4B)
    have hdc : dc ≠ 0 := bne_iff_ne.mp (by simpa [dc] using hdcB)
    have hd : ∀ i : Fin 5,
        rowDotN (![s0, s1, s2, s3, s4] i).val (v 0) (v 1) (v 2) (v 3) (v 4) =
          dc * bZ (![s0, s1, s2, s3, s4] i).val := by
      intro i; fin_cases i
      · exact hr0
      · exact hr1
      · exact hr2
      · exact hr3
      · exact hr4
    have hyv := hy_of_int hdc hd
    cases ht2 : (tagAt r == 2) with
    | true =>
      have hm := htag
      rw [if_pos ht2] at hm
      have hm4B := band_right hm
      have hm3s := band_left hm
      have hm3B := band_right hm3s
      have hm2s := band_left hm3s
      have hm2B := band_right hm2s
      have hm1s := band_left hm2s
      have hm1B := band_right hm1s
      have hm0B := band_left hm1s
      have hm0 : orbitNum (of20 (oAt r)) 0 * dc = v 0 * orbitDen (of20 (oAt r)) :=
        beq_iff_eq.mp (by simpa [v, dc] using hm0B)
      have hm1 : orbitNum (of20 (oAt r)) 1 * dc = v 1 * orbitDen (of20 (oAt r)) :=
        beq_iff_eq.mp (by simpa [v, dc] using hm1B)
      have hm2 : orbitNum (of20 (oAt r)) 2 * dc = v 2 * orbitDen (of20 (oAt r)) :=
        beq_iff_eq.mp (by simpa [v, dc] using hm2B)
      have hm3 : orbitNum (of20 (oAt r)) 3 * dc = v 3 * orbitDen (of20 (oAt r)) :=
        beq_iff_eq.mp (by simpa [v, dc] using hm3B)
      have hm4 : orbitNum (of20 (oAt r)) 4 * dc = v 4 * orbitDen (of20 (oAt r)) :=
        beq_iff_eq.mp (by simpa [v, dc] using hm4B)
      let o : Fin 20 := of20 (oAt r)
      refine ⟨o, ?_⟩
      ext j
      have hmatch : orbitNum o j * dc = v j * orbitDen o := by
        fin_cases j
        · simpa [o] using hm0
        · simpa [o] using hm1
        · simpa [o] using hm2
        · simpa [o] using hm3
        · simpa [o] using hm4
      have hden : (orbitDen o : ℝ) ≠ 0 := Int.cast_ne_zero.2 (orbitDen_ne_zero o)
      have hdcR : (dc : ℝ) ≠ 0 := Int.cast_ne_zero.2 hdc
      simp [orbitPoint_apply, hyv]
      field_simp [hden, hdcR]
      norm_cast
      linarith [hmatch]
    | false =>
      have hyi : ∀ j, y j = (v j : ℝ) / (dc : ℝ) := hyv
      cases hk : (failKindAt r == 0) with
      | true =>
        have hch := (extreme_in_chamber hy hnn).1 (of14 (failRowAt r))
        have hfr : failRowAt r < 14 := failRowAt_lt hr
        have hiF : (of14 (failRowAt r)).val = failRowAt r := Nat.mod_eq_of_lt hfr
        have hdot : rowDotN (failRowAt r) (v 0) (v 1) (v 2) (v 3) (v 4) =
            intDot5 (chamberAZ (of14 (failRowAt r))) v := by
          have := rowDotN_eq (of14 (failRowAt r)) v
          rwa [hiF] at this
        have hbz : bZ (failRowAt r) = chamberBZ (of14 (failRowAt r)) := by
          have := bZ_eq (of14 (failRowAt r))
          rwa [hiF] at this
        have hvil := htag
        rw [if_neg (Bool.eq_false_iff.mp ht2), if_pos hk] at hvil
        have hinter : ⟪chamberA (of14 (failRowAt r)), y⟫ =
            (intDot5 (chamberAZ (of14 (failRowAt r))) v : ℝ) / (dc : ℝ) := by
          simp [inner_chamber, hyi, intDot5, Fin.sum_univ_five]
          field_simp [Int.cast_ne_zero.2 hdc]
        by_cases hdpos : (0 : ℤ) < dc
        · have hrow : bZ (failRowAt r) * dc <
              rowDotN (failRowAt r) (v 0) (v 1) (v 2) (v 3) (v 4) := by
            have hd : 0 < dAt r := by simpa [dc] using hdpos
            rw [if_pos hd] at hvil
            exact of_decide_eq_true (by simpa [v, dc] using hvil)
          have : ¬ ⟪chamberA (of14 (failRowAt r)), y⟫ ≤
              chamberB (of14 (failRowAt r)) := by
            have hdcR : (0 : ℝ) < dc := Int.cast_pos.2 hdpos
            rw [hinter, chamberB, div_le_iff₀ hdcR, ← hbz, ← hdot]
            have hlt : (bZ (failRowAt r) : ℝ) * (dc : ℝ) <
                (rowDotN (failRowAt r) (v 0) (v 1) (v 2) (v 3) (v 4) : ℝ) := by
              exact_mod_cast hrow
            linarith
          exact (this hch).elim
        · have hdneg : dc < 0 := lt_of_le_of_ne (le_of_not_gt hdpos) hdc
          have hrow : rowDotN (failRowAt r) (v 0) (v 1) (v 2) (v 3) (v 4) <
              bZ (failRowAt r) * dc := by
            have hn : ¬ (0 < dAt r) := by simpa [dc] using hdpos
            rw [if_neg hn] at hvil
            exact of_decide_eq_true (by simpa [v, dc] using hvil)
          have : ¬ ⟪chamberA (of14 (failRowAt r)), y⟫ ≤
              chamberB (of14 (failRowAt r)) := by
            have hdcR : (dc : ℝ) < 0 := Int.cast_lt_zero.2 hdneg
            rw [hinter, chamberB, div_le_iff_of_neg hdcR, ← hbz, ← hdot]
            have hlt : (rowDotN (failRowAt r) (v 0) (v 1) (v 2) (v 3) (v 4) : ℝ) <
                (bZ (failRowAt r) : ℝ) * (dc : ℝ) := by
              exact_mod_cast hrow
            linarith
          exact (this hch).elim
      | false =>
        have hfew : origCount v dc < 5 := by
          have h := htag
          rw [if_neg (Bool.eq_false_iff.mp ht2),
            if_neg (Bool.eq_false_iff.mp hk)] at h
          exact of_decide_eq_true (by simpa [v, dc] using h)
        have hceq' : origCount v dc =
            (Finset.univ.filter (fun i : Fin 28 => ⟪q28A i, y⟫ = 1)).card := by
          rw [origCount_eq_filter]
          congr 1
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hinter : ⟪q28A i, y⟫ = (intDot5 (q28AZ i) v : ℝ) / (dc : ℝ) := by
            simp [inner_q28A_coords, hyi, intDot5, Fin.sum_univ_five]
            field_simp [Int.cast_ne_zero.2 hdc]
          constructor
          · intro hdot
            simp [hinter, hdot, Int.cast_ne_zero.2 hdc]
          · intro htight
            have : (intDot5 (q28AZ i) v : ℝ) / (dc : ℝ) = 1 := by
              simpa [hinter] using htight
            have : (intDot5 (q28AZ i) v : ℝ) = (dc : ℝ) :=
              (div_eq_one_iff_eq (Int.cast_ne_zero.2 hdc)).mp this
            exact_mod_cast this
        have : 5 ≤ origCount v dc := by
          simpa [hceq', q28B] using spindle_tight_card hy
        omega

lemma extreme_signed_orbit {x : EuclideanSpace ℝ (Fin 5)}
    (hx : x ∈ extremePoints ℝ (Hpoly q28A q28B)) :
    ∃ o s, x = flipPoint s (orbitPoint o) := by
  let y := flipPoint (signOf x) x
  have hnn : ∀ j : Fin 4, 0 ≤ y j.castSucc := fun j => flip_signOf_nonneg x j
  have hy : y ∈ extremePoints ℝ (Hpoly q28A q28B) := flipPoint_extreme (signOf x) hx
  obtain ⟨o, ho⟩ := extreme_nonneg_orbit hy hnn
  refine ⟨o, signOf x, ?_⟩
  calc
    x = flipPoint (signOf x) (flipPoint (signOf x) x) :=
      (flipPoint_flipPoint (signOf x) x).symm
    _ = flipPoint (signOf x) y := rfl
    _ = flipPoint (signOf x) (orbitPoint o) := by rw [ho]

lemma orbit_rep_unique {x : EuclideanSpace ℝ (Fin 5)} {o1 o2 : Fin 20} {s1 s2 : Fin 16}
    (h1 : x = flipPoint s1 (orbitPoint o1))
    (h2 : x = flipPoint s2 (orbitPoint o2)) : o1 = o2 := by
  have heq : orbitPoint o1 = flipPoint (signXor s1 s2) (orbitPoint o2) := by
    calc
      orbitPoint o1 = flipPoint s1 x := by rw [h1, flipPoint_flipPoint]
      _ = flipPoint s1 (flipPoint s2 (orbitPoint o2)) := by rw [h2]
      _ = flipPoint (signXor s1 s2) (orbitPoint o2) := flipPoint_comp _ _ _
  refine orbitPoint_inj ?_
  apply PiLp.ext
  intro j
  have hj : orbitPoint o1 j =
      (signCoord (signXor s1 s2) j : ℝ) * orbitPoint o2 j := by
    simpa [flipPoint_apply] using congrArg (fun z : EuclideanSpace ℝ (Fin 5) => z j) heq
  fin_cases j <;> simp at hj ⊢
  · have n1 := orbitPoint_nonneg o1 (0 : Fin 4)
    have n2 := orbitPoint_nonneg o2 (0 : Fin 4)
    have hs : signCoord (signXor s1 s2) 0 = 1 ∨ signCoord (signXor s1 s2) 0 = -1 := by
      unfold signCoord; split_ifs <;> simp
    rcases hs with hs | hs <;> simp [hs] at hj n1 n2 ⊢ <;> nlinarith
  · have n1 := orbitPoint_nonneg o1 (1 : Fin 4)
    have n2 := orbitPoint_nonneg o2 (1 : Fin 4)
    have hs : signCoord (signXor s1 s2) 1 = 1 ∨ signCoord (signXor s1 s2) 1 = -1 := by
      unfold signCoord; split_ifs <;> simp
    rcases hs with hs | hs <;> simp [hs] at hj n1 n2 ⊢ <;> nlinarith
  · have n1 := orbitPoint_nonneg o1 (2 : Fin 4)
    have n2 := orbitPoint_nonneg o2 (2 : Fin 4)
    have hs : signCoord (signXor s1 s2) 2 = 1 ∨ signCoord (signXor s1 s2) 2 = -1 := by
      unfold signCoord; split_ifs <;> simp
    rcases hs with hs | hs <;> simp [hs] at hj n1 n2 ⊢ <;> nlinarith
  · have n1 := orbitPoint_nonneg o1 (3 : Fin 4)
    have n2 := orbitPoint_nonneg o2 (3 : Fin 4)
    have hs : signCoord (signXor s1 s2) 3 = 1 ∨ signCoord (signXor s1 s2) 3 = -1 := by
      unfold signCoord; split_ifs <;> simp
    rcases hs with hs | hs <;> simp [hs] at hj n1 n2 ⊢ <;> nlinarith
  · simpa [signCoord_last] using hj


theorem solution :
    (∀ x : EuclideanSpace ℝ (Fin 5),
      x ∈ extremePoints ℝ (Hpoly q28A q28B) →
        ∃ o : Fin 20, ∃ s : Fin 16, x = flipPoint s (orbitPoint o)) ∧
    (∀ x : EuclideanSpace ℝ (Fin 5), ∀ o1 o2 : Fin 20, ∀ s1 s2 : Fin 16,
      x = flipPoint s1 (orbitPoint o1) →
      x = flipPoint s2 (orbitPoint o2) → o1 = o2) ∧
    q28U = flipPoint 0 (orbitPoint 1) ∧
    q28V = flipPoint 0 (orbitPoint 0) ∧
    (∀ s : Fin 16, flipPoint s (orbitPoint 1) = q28U) ∧
    (∀ s : Fin 16, flipPoint s (orbitPoint 0) = q28V) := by
  refine ⟨?hextr, ?huniq, ?hU, ?hV, ?hUf, ?hVf⟩
  · intro x hx
    exact extreme_signed_orbit hx
  · intro x o1 o2 s1 s2 h1 h2
    exact orbit_rep_unique h1 h2
  · rw [orbitPoint_U, flipPoint_zero]
  · rw [orbitPoint_V, flipPoint_zero]
  · intro s
    simpa [orbitPoint_U] using flipPoint_U s
  · intro s
    simpa [orbitPoint_V] using flipPoint_V s
