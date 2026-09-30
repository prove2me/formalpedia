-- Prove2me | solution 1 for Hirsch.q28_adj_to_orbit
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-06T01:35:28.53653+00:00
-- url     : https://prove2.me/submissions/372d9245-e6e0-4dae-b2fb-217d278b39b1

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert
import Theorems.Thm_Hirsch_q28_finite_certificate
import Theorems.Thm_Hirsch_q28_extreme_classification
import Theorems.Thm_Hirsch_q28_cardAt_eq_popcount_low
import Theorems.Thm_Hirsch_q28_cardAt_eq_popcount_high

open scoped RealInnerProductSpace
open Set Hirsch Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

/-! Adjacency on the Q28 polar descends to stored orbits or QuotientAdj. -/

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


lemma range_eq_Iio_nat (n : ℕ) : Finset.range n = Finset.Iio n := by
  ext x
  simp [Finset.mem_range, Finset.mem_Iio]

lemma commonActive_bits (o1 o2 : Fin 20) (s : Fin 16) :
    (Finset.univ.filter (fun i : Fin 28 =>
      intDotFlip o1 0 i = orbitDen o1 ∧
        intDotFlip o2 s i = orbitDen o2)) =
      (Finset.univ.filter (fun i : Fin 28 =>
        (Nat.land (tightMask o1 0) (tightMask o2 s)).testBit i.val = true)) := by
  ext i
  have hb1 := mask_bit o1 0 i
  have hb2 := mask_bit o2 s i
  have hbit :
      (Nat.land (tightMask o1 0) (tightMask o2 s)).testBit i.val = true ↔
        (tightMask o1 0).testBit i.val = true ∧
          (tightMask o2 s).testBit i.val = true := by
    simp [Nat.testBit_and, Bool.and_eq_true]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hbit, hb1, hb2]

lemma popcount28_eq_count (m : ℕ) :
    popcount28 m = Nat.count (fun i => m.testBit i = true) 28 := by
  simp [popcount28, Nat.count_succ, Nat.count_zero]

lemma popcount28_eq_filter (m : ℕ) :
    popcount28 m =
      (Finset.univ.filter (fun i : Fin 28 => m.testBit i.val = true)).card := by
  rw [popcount28_eq_count, Nat.count_eq_card_filter_range, range_eq_Iio_nat,
    ← Fin.map_valEmbedding_univ, Finset.filter_map]
  simp [Finset.card_map]

lemma cardAt_eq_popcount :
    ∀ (o1 o2 : Fin 20) (s : Fin 16),
      commonActiveCard o1 o2 s =
        popcount28 (Nat.land (tightMask o1 0) (tightMask o2 s)) := by
  intro o1 o2 s
  by_cases h : o1.val < 10
  · exact q28_cardAt_eq_popcount_low o1 o2 s h
  · exact q28_cardAt_eq_popcount_high o1 o2 s (le_of_not_gt h)

lemma commonActive_filter (o1 o2 : Fin 20) (s : Fin 16) :
    (Finset.univ.filter (fun i : Fin 28 =>
      ⟪q28A i, orbitPoint o1⟫ = 1 ∧
        ⟪q28A i, flipPoint s (orbitPoint o2)⟫ = 1)).card =
      commonActiveCard o1 o2 s := by
  rw [commonActive_dots, commonActive_bits, cardAt_eq_popcount, popcount28_eq_filter]

theorem solution :
    ∀ x y : EuclideanSpace ℝ (Fin 5),
      Adj (Hpoly q28A q28B) x y →
        ∃ o1 o2 : Fin 20, ∃ s1 s2 : Fin 16,
          x = flipPoint s1 (orbitPoint o1) ∧
          y = flipPoint s2 (orbitPoint o2) ∧
          (o1 = o2 ∨ QuotientAdj o1 o2) := by
  intro x y hAdj
  have hx := adj_left_extreme hAdj
  have hy := adj_right_extreme hAdj
  obtain ⟨o1, s1, hxeq⟩ := q28_extreme_classification.1 x hx
  obtain ⟨o2, s2, hyeq⟩ := q28_extreme_classification.1 y hy
  have hAdj' :
      Adj (Hpoly q28A q28B) (orbitPoint o1)
        (flipPoint (signXor s1 s2) (orbitPoint o2)) := by
    have hx' : flipPoint s1 x = orbitPoint o1 := by
      nth_rw 1 [hxeq]
      rw [flipPoint_flipPoint]
    have hy' : flipPoint s1 y =
        flipPoint (signXor s1 s2) (orbitPoint o2) := by
      nth_rw 1 [hyeq]
      rw [flipPoint_comp]
    have hAdj'' := adj_flip s1 hAdj
    rwa [hx', hy'] at hAdj''
  have hcard := adj_common_active_ge_four hAdj'
  have hceq := commonActive_filter o1 o2 (signXor s1 s2)
  have : 4 ≤ commonActiveCard o1 o2 (signXor s1 s2) := by
    simpa [hceq] using hcard
  refine ⟨o1, o2, s1, s2, hxeq, hyeq, ?_⟩
  exact four_actives_in_quotient o1 o2 (signXor s1 s2) this
