-- Prove2me | solution 1 for MovingSofa.boundedVariationOn_of_mem_exposedEdge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:25:48.792131+00:00
-- url     : https://prove2.me/submissions/322ccab5-615f-4983-8996-854bacf61419

import Mathlib
import Definitions.Def_MovingSofa_Geometry_Basic
import Definitions.Def_MovingSofa_Geometry_Plane
import Definitions.Def_MovingSofa_Geometry_Contacts

noncomputable section

namespace EdgeAux
open MovingSofa

theorem bdd (K : ConvexBody Point) (v : Point) :
    BddAbove ((fun p : Point ↦ inner ℝ p v) '' (K : Set Point)) :=
  (K.isCompact.image (by fun_prop)).bddAbove

theorem inner_le_sv (K : ConvexBody Point) {p : Point}
    (hp : p ∈ K) (t : Real.Angle) : inner ℝ p (normalVector t) ≤ supportValue K t :=
  le_csSup (bdd K _) ⟨p, hp, rfl⟩

theorem decomp (p : Point) (t : Real.Angle) :
    p = inner ℝ p (normalVector t) • normalVector t +
      inner ℝ p (tangentVector t) • tangentVector t := by
  have h := Real.Angle.cos_sq_add_sin_sq t
  ext i
  fin_cases i
  · simp [normalVector, tangentVector, frame, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_two]
    linear_combination (-(p 0) * h)
  · simp [normalVector, tangentVector, frame, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_two]
    linear_combination (-(p 1) * h)

theorem edge_nonempty (K : ConvexBody Point) (t : Real.Angle) : (exposedEdge K t).Nonempty := by
  have hcont : Continuous fun p : Point ↦ inner ℝ p (normalVector t) := by fun_prop
  obtain ⟨p, hp, hmax⟩ := K.isCompact.exists_isMaxOn K.nonempty hcont.continuousOn
  refine ⟨p, hp, ?_⟩
  show inner ℝ p (normalVector t) = supportValue K t
  apply le_antisymm (inner_le_sv K hp t)
  exact csSup_le ⟨_, p, hp, rfl⟩ (by rintro _ ⟨q, hq, rfl⟩; exact hmax hq)

theorem edge_compact (K : ConvexBody Point) (t : Real.Angle) : IsCompact (exposedEdge K t) := by
  apply K.isCompact.inter_right
  exact isClosed_eq (by fun_prop) continuous_const

theorem mem_edge_of (K : ConvexBody Point) (t : Real.Angle) (q : Point)
    (hq : q ∈ exposedEdge K t) :
    q = supportValue K t • normalVector t + inner ℝ q (tangentVector t) • tangentVector t := by
  have h2 : inner ℝ q (normalVector t) = supportValue K t := hq.2
  conv_lhs => rw [decomp q t]
  rw [h2]

theorem fst_mem (K : ConvexBody Point) (t : Real.Angle) :
    (edgeVertices K t).1 ∈ exposedEdge K t := by
  have hc := (edge_compact K t).image (f := fun p : Point ↦ inner ℝ p (tangentVector t)) (by fun_prop)
  have hne := (edge_nonempty K t).image (fun p : Point ↦ inner ℝ p (tangentVector t))
  obtain ⟨q, hq, hqe⟩ := hc.sSup_mem hne
  have := mem_edge_of K t q hq
  simp only [edgeVertices]
  rw [← hqe, ← this]
  exact hq

theorem snd_mem (K : ConvexBody Point) (t : Real.Angle) :
    (edgeVertices K t).2 ∈ exposedEdge K t := by
  have hc := (edge_compact K t).image (f := fun p : Point ↦ inner ℝ p (tangentVector t)) (by fun_prop)
  have hne := (edge_nonempty K t).image (fun p : Point ↦ inner ℝ p (tangentVector t))
  obtain ⟨q, hq, hqe⟩ := hc.sInf_mem hne
  have := mem_edge_of K t q hq
  simp only [edgeVertices]
  rw [← hqe, ← this]
  exact hq

end EdgeAux

namespace BVAux
open MovingSofa EdgeAux

theorem norm_n (t : Real.Angle) : ‖normalVector t‖ = 1 := by
  have h := Real.Angle.cos_sq_add_sin_sq t
  rw [EuclideanSpace.norm_eq]
  simp [normalVector, frame, Fin.sum_univ_two, h]

theorem norm_tau (t : Real.Angle) : ‖tangentVector t‖ = 1 := by
  have h := Real.Angle.cos_sq_add_sin_sq t
  rw [EuclideanSpace.norm_eq]
  have h' : t.sin ^ 2 + t.cos ^ 2 = 1 := by rw [add_comm]; exact h
  simp [tangentVector, frame, Fin.sum_univ_two, h']

theorem n_add (s δ : ℝ) : normalVector ((s + δ : ℝ) : Real.Angle) =
    Real.cos δ • normalVector (s : Real.Angle) + Real.sin δ • tangentVector (s : Real.Angle) := by
  ext i
  fin_cases i
  · simp [-Real.Angle.coe_add, normalVector, tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_add, Real.sin_add]; ring
  · simp [-Real.Angle.coe_add, normalVector, tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_add, Real.sin_add]; ring

theorem tau_add (s δ : ℝ) : tangentVector ((s + δ : ℝ) : Real.Angle) =
    Real.cos δ • tangentVector (s : Real.Angle) - Real.sin δ • normalVector (s : Real.Angle) := by
  ext i
  fin_cases i
  · simp [-Real.Angle.coe_add, normalVector, tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_add, Real.sin_add]; ring
  · simp [-Real.Angle.coe_add, normalVector, tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_add, Real.sin_add]; ring

theorem inner_le_R {R : ℝ} {q v : Point} (hq : ‖q‖ ≤ R) (hv : ‖v‖ ≤ 1) :
    inner ℝ q v ≤ R := by
  have h1 := real_inner_le_norm q v
  have h2 : ‖q‖ * ‖v‖ ≤ R * 1 :=
    mul_le_mul hq hv (norm_nonneg _) ((norm_nonneg _).trans hq)
  linarith

theorem abs_inner_le_R {R : ℝ} {q v : Point} (hq : ‖q‖ ≤ R) (hv : ‖v‖ ≤ 1) :
    |inner ℝ q v| ≤ R := by
  have h1 := abs_real_inner_le_norm q v
  have h2 : ‖q‖ * ‖v‖ ≤ R * 1 :=
    mul_le_mul hq hv (norm_nonneg _) ((norm_nonneg _).trans hq)
  linarith

theorem step (K : ConvexBody Point) (R : ℝ) (hR : ∀ x ∈ (K : Set Point), ‖x‖ ≤ R)
    (s t : ℝ) (hst : s < t) (p q : Point)
    (hp : p ∈ exposedEdge K (s : Real.Angle)) (hq : q ∈ exposedEdge K (t : Real.Angle)) :
    ‖q - p‖ ≤ 3 * (inner ℝ q (tangentVector (t : Real.Angle)) -
        inner ℝ p (tangentVector (s : Real.Angle))) + 8 * R * (t - s) := by
  set δ := t - s with hδ
  have htd : t = s + δ := by rw [hδ]; ring
  set ns := normalVector (s : Real.Angle)
  set ts := tangentVector (s : Real.Angle)
  have hpR := hR p hp.1
  have hqR := hR q hq.1
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hpR
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  -- support inequalities
  have h1 : inner ℝ q ns ≤ inner ℝ p ns := by
    have := inner_le_sv K hq.1 (s : Real.Angle)
    have h2 : inner ℝ p ns = supportValue K s := hp.2
    linarith
  have h2 : inner ℝ p (normalVector (t : Real.Angle)) ≤ inner ℝ q (normalVector (t : Real.Angle)) := by
    have := inner_le_sv K hp.1 (t : Real.Angle)
    have h2 : inner ℝ q (normalVector (t : Real.Angle)) = supportValue K t := hq.2
    linarith
  set a := inner ℝ (q - p) ns with ha_def
  set b := inner ℝ (q - p) ts with hb_def
  have ha : a ≤ 0 := by rw [ha_def, inner_sub_left]; linarith
  have he : 0 ≤ a * Real.cos δ + b * Real.sin δ := by
    have : inner ℝ (q - p) (normalVector (t : Real.Angle)) = a * Real.cos δ + b * Real.sin δ := by
      rw [htd, n_add, inner_add_right, real_inner_smul_right, real_inner_smul_right]; ring
    rw [← this, inner_sub_left]; linarith
  have hnorm : ‖q - p‖ ≤ |a| + |b| := by
    have hd := decomp (q - p) (s : Real.Angle)
    calc ‖q - p‖ = ‖a • ns + b • ts‖ := by rw [← hd]
      _ ≤ ‖a • ns‖ + ‖b • ts‖ := norm_add_le _ _
      _ = |a| + |b| := by rw [norm_smul, norm_smul, norm_n, norm_tau]; simp
  have hT : inner ℝ q ts - inner ℝ p ts =
      (inner ℝ q (tangentVector (t : Real.Angle)) - inner ℝ p ts) +
        inner ℝ q (ts - tangentVector (t : Real.Angle)) := by
    rw [inner_sub_right]; ring
  have hb : b = inner ℝ q ts - inner ℝ p ts := by rw [hb_def, inner_sub_left]
  have hgq := abs_inner_le_R hqR (le_of_eq (norm_tau (t : Real.Angle)))
  have hgp := abs_inner_le_R hpR (le_of_eq (norm_tau (s : Real.Angle)))
  rcases le_or_gt δ 1 with hsmall | hbig
  · have hc : 1 / 2 ≤ Real.cos δ := by
      have := (Real.one_sub_sq_div_two_le_cos : 1 - δ ^ 2 / 2 ≤ Real.cos δ); nlinarith
    have hsn : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ0 (by linarith [Real.pi_gt_three])
    have hsl : Real.sin δ ≤ δ := Real.sin_le hδ0.le
    have hcl : Real.cos δ ≤ 1 := Real.cos_le_one δ
    have hb0 : 0 ≤ b := by
      by_contra hneg; rw [not_le] at hneg
      nlinarith
    have haa : -a ≤ 2 * b := by nlinarith
    have hlip : ‖ts - tangentVector (t : Real.Angle)‖ ≤ 2 * δ := by
      have hc2 := (Real.one_sub_sq_div_two_le_cos : 1 - δ ^ 2 / 2 ≤ Real.cos δ)
      have : ts - tangentVector (t : Real.Angle) = (1 - Real.cos δ) • ts + Real.sin δ • ns := by
        rw [htd, tau_add]; module
      rw [this]
      calc ‖(1 - Real.cos δ) • ts + Real.sin δ • ns‖
          ≤ ‖(1 - Real.cos δ) • ts‖ + ‖Real.sin δ • ns‖ := norm_add_le _ _
        _ = (1 - Real.cos δ) + Real.sin δ := by
          rw [norm_smul, norm_smul, norm_n, norm_tau, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith), abs_of_pos hsn]; ring
        _ ≤ 2 * δ := by nlinarith
    have hqv : inner ℝ q (ts - tangentVector (t : Real.Angle)) ≤ R * (2 * δ) := by
      have h1 := real_inner_le_norm q (ts - tangentVector (t : Real.Angle))
      have h2 : ‖q‖ * ‖ts - tangentVector (t : Real.Angle)‖ ≤ R * (2 * δ) :=
        mul_le_mul hqR hlip (norm_nonneg _) hR0
      linarith
    rw [abs_of_nonpos ha, abs_of_nonneg hb0] at hnorm
    nlinarith
  · have hd2 : ‖q - p‖ ≤ 2 * R := by
      have := norm_sub_le q p; linarith
    rw [abs_le] at hgq hgp
    nlinarith

theorem bv_of_edge (K : ConvexBody Point)
    (f : ℝ → Point) (hf : ∀ t : ℝ, f t ∈ exposedEdge K (t : Real.Angle)) (a b : ℝ) :
    BoundedVariationOn f (Set.Icc a b) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp K.isCompact.isBounded
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR _ (hf 0).1)
  set g : ℝ → ℝ := fun t ↦ inner ℝ (f t) (tangentVector (t : Real.Angle)) with hg
  have hgR : ∀ t, |g t| ≤ R := fun t ↦
    abs_inner_le_R (hR _ (hf t).1) (le_of_eq (norm_tau _))
  have hstep : ∀ s t : ℝ, s ≤ t → dist (f t) (f s) ≤ 3 * (g t - g s) + 8 * R * (t - s) := by
    intro s t hst
    rcases eq_or_lt_of_le hst with h | h
    · subst h; simp
    · rw [dist_eq_norm]; exact step K R hR s t h _ _ (hf s) (hf t)
  unfold BoundedVariationOn
  apply ne_top_of_le_ne_top (@ENNReal.ofReal_ne_top (6 * R + 8 * R * (b - a)))
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  simp only
  have : ∀ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) =
      ENNReal.ofReal (dist (f (u (i + 1))) (f (u i))) := fun i _ ↦ edist_dist _ _
  rw [Finset.sum_congr rfl this, ← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ dist_nonneg)]
  apply ENNReal.ofReal_le_ofReal
  calc ∑ i ∈ Finset.range n, dist (f (u (i + 1))) (f (u i))
      ≤ ∑ i ∈ Finset.range n, ((3 * g (u (i + 1)) + 8 * R * u (i + 1)) -
          (3 * g (u i) + 8 * R * u i)) := by
        apply Finset.sum_le_sum
        intro i _
        have := hstep (u i) (u (i + 1)) (hu (Nat.le_succ i))
        linarith
    _ = (3 * g (u n) + 8 * R * u n) - (3 * g (u 0) + 8 * R * u 0) :=
        Finset.sum_range_sub (fun i ↦ 3 * g (u i) + 8 * R * u i) n
    _ ≤ 6 * R + 8 * R * (b - a) := by
        have h1 := (hus n).2
        have h2 := (hus 0).1
        have h3 := hgR (u n)
        have h4 := hgR (u 0)
        rw [abs_le] at h3 h4
        nlinarith

end BVAux

open MovingSofa EdgeAux BVAux in
theorem solution (K : ConvexBody Point)
    (f : ℝ → Point) (hf : ∀ t : ℝ, f t ∈ exposedEdge K (t : Real.Angle)) (a b : ℝ) :
    BoundedVariationOn f (Set.Icc a b) :=
  bv_of_edge K f hf a b

