-- Prove2me | solution 1 for Hirsch.cut_face_access_of_outer_diameter
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-06T21:06:56.06265+00:00
-- url     : https://prove2.me/submissions/753d90ed-5af0-4c84-8de6-395bc4646e79

import Definitions.Def_Hirsch_model
import Mathlib

-- BEGIN Solutions/PolynomialHalfspaceEdge.lean

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCut

variable {d : ℕ}

lemma inner_combo (c p q : EuclideanSpace ℝ (Fin d)) (α β : ℝ) :
    ⟪c, α • p + β • q⟫ = α * ⟪c, p⟫ + β * ⟪c, q⟫ := by
  simp [inner_add_right, inner_smul_right]

/-- A retained old edge stays an edge after adding one halfspace. -/
lemma retained_edge
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    {p q : EuclideanSpace ℝ (Fin d)} (hadj : Adj Q p q)
    (hp : ⟪c, p⟫ ≤ b) (hq : ⟪c, q⟫ ≤ b) :
    Adj (Q ∩ {x | ⟪c, x⟫ ≤ b}) p q := by
  refine ⟨hadj.1, hadj.2.mono Set.inter_subset_left ?_⟩
  intro x hx
  refine ⟨hadj.2.subset hx, ?_⟩
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hx
  change ⟪c, α • p + β • q⟫ ≤ b
  rw [inner_combo]
  have h1 := mul_le_mul_of_nonneg_left hp hα
  have h2 := mul_le_mul_of_nonneg_left hq hβ
  have h3 : α * b + β * b = b := by rw [← add_mul, hαβ, one_mul]
  linarith

/-- The first part of an old edge crossing the cut plane is an edge of the
clipped polytope. Its new endpoint lies exactly on the cut plane. -/
lemma clip_crossing_edge
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    {p q : EuclideanSpace ℝ (Fin d)} (hadj : Adj Q p q)
    (hp : ⟪c, p⟫ < b) (hq : b ≤ ⟪c, q⟫) :
    ∃ z : EuclideanSpace ℝ (Fin d), ⟪c, z⟫ = b ∧
      Adj (Q ∩ {x | ⟪c, x⟫ ≤ b}) p z := by
  let D : ℝ := ⟪c, q⟫ - ⟪c, p⟫
  have hD : 0 < D := by dsimp [D]; linarith
  let t : ℝ := (b - ⟪c, p⟫) / D
  have ht : 0 < t := div_pos (sub_pos.mpr hp) hD
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ hD).2
    dsimp [D]
    linarith
  have htD : t * D = b - ⟪c, p⟫ := div_mul_cancel₀ _ hD.ne'
  let z : EuclideanSpace ℝ (Fin d) := (1 - t) • p + t • q
  have hz : ⟪c, z⟫ = b := by
    rw [show z = (1 - t) • p + t • q from rfl, inner_combo]
    dsimp [D] at htD
    nlinarith
  have hzseg : z ∈ segment ℝ p q :=
    ⟨1 - t, t, by linarith, ht.le, by ring, rfl⟩
  have heq : segment ℝ p z = {w | w ∈ segment ℝ p q ∧ ⟪c, w⟫ ≤ b} := by
    ext w
    constructor
    · intro hw
      have hwold : w ∈ segment ℝ p q :=
        (convex_segment p q).segment_subset (left_mem_segment ℝ p q) hzseg hw
      refine ⟨hwold, ?_⟩
      obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hw
      rw [inner_combo, hz]
      have h1 := mul_le_mul_of_nonneg_left hp.le hα
      have h2 : α * b + β * b = b := by rw [← add_mul, hαβ, one_mul]
      linarith
    · rintro ⟨hw, hwb⟩
      obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hw
      have hαone : α = 1 - β := by linarith
      have hinner : ⟪c, w⟫ = ⟪c, p⟫ + β * D := by
        rw [← hcomb, inner_combo, hαone]
        dsimp [D]
        ring
      have hβt : β ≤ t := by
        rw [hinner] at hwb
        nlinarith
      let γ : ℝ := β / t
      have hγ0 : 0 ≤ γ := div_nonneg hβ ht.le
      have hγ1 : γ ≤ 1 := by
        apply (div_le_iff₀ ht).2
        linarith
      have hγt : γ * t = β := div_mul_cancel₀ _ ht.ne'
      have hflat : (1 - γ) • p + γ • z =
          (1 - γ * t) • p + (γ * t) • q := by
        dsimp [z]
        module
      refine ⟨1 - γ, γ, by linarith, hγ0, by ring, ?_⟩
      rw [hflat, hγt, ← hαone]
      exact hcomb
  have hpz : p ≠ z := by
    intro h
    exact hp.ne ((congrArg (fun x : EuclideanSpace ℝ (Fin d) => ⟪c, x⟫) h).trans hz)
  refine ⟨z, hz, hpz, ?_, ?_⟩
  · intro w hw
    rw [heq] at hw
    exact ⟨hadj.2.subset hw.1, hw.2⟩
  · intro x hx y hy w hw hop
    rw [heq] at hw ⊢
    exact ⟨hadj.2.left_mem_of_mem_openSegment hx.1 hy.1 hw.1 hop, hx.2⟩


end HirschCut
end


-- BEGIN Solutions/PolynomialHalfspaceVertex.lean

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCut

/-- A vertex strictly on the retained side of a cut was already a vertex of
 the convex outer set. New vertices created by one cut lie on its plane. -/
lemma strict_cut_extreme_to_parent {d : ℕ}
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hconv : Convex ℝ Q)
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    {u : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}))
    (hustrict : ⟪c, u⟫ < b) : u ∈ extremePoints ℝ Q := by
  refine ⟨hu.1.1, ?_⟩
  intro x hx y hy hopen
  obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hopen
  let Δ : ℝ := b - ⟪c, u⟫
  have hΔ : 0 < Δ := sub_pos.mpr hustrict
  let A : ℝ := ⟪c, x⟫ - ⟪c, u⟫
  let C : ℝ := ⟪c, y⟫ - ⟪c, u⟫
  let D : ℝ := Δ + |A| + |C| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hΔD : Δ ≤ D := by
    dsimp [D]
    linarith [abs_nonneg A, abs_nonneg C]
  let ε : ℝ := Δ / D
  have hε : 0 < ε := div_pos hΔ hD
  have hε1 : ε ≤ 1 := by
    apply (div_le_iff₀ hD).2
    simpa only [one_mul] using hΔD
  have hεD : ε * D = Δ := div_mul_cancel₀ _ hD.ne'
  have hAD : A ≤ D := by
    have h := le_abs_self A
    dsimp [D]
    linarith [abs_nonneg C]
  have hCD : C ≤ D := by
    have h := le_abs_self C
    dsimp [D]
    linarith [abs_nonneg A]
  let x' : EuclideanSpace ℝ (Fin d) := (1 - ε) • u + ε • x
  let y' : EuclideanSpace ℝ (Fin d) := (1 - ε) • u + ε • y
  have hxQ : x' ∈ Q :=
    hconv hu.1.1 hx (by linarith) hε.le (by ring)
  have hyQ : y' ∈ Q :=
    hconv hu.1.1 hy (by linarith) hε.le (by ring)
  have hxcut : ⟪c, x'⟫ ≤ b := by
    have h := mul_le_mul_of_nonneg_left hAD hε.le
    rw [hεD] at h
    dsimp [x']
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    dsimp [A, Δ] at h
    nlinarith
  have hycut : ⟪c, y'⟫ ≤ b := by
    have h := mul_le_mul_of_nonneg_left hCD hε.le
    rw [hεD] at h
    dsimp [y']
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    dsimp [C, Δ] at h
    nlinarith
  have hopen' : u ∈ openSegment ℝ x' y' := by
    refine ⟨α, β, hα, hβ, hαβ, ?_⟩
    have hflat : α • x' + β • y' =
        (1 - ε) • u + ε • (α • x + β • y) := by
      dsimp [x', y']
      rw [show α = 1 - β by linarith]
      module
    rw [hflat, hcomb, ← add_smul]
    have hcoeff : (1 - ε) + ε = 1 := by ring
    rw [hcoeff, one_smul]
  have hxu : x' = u := hu.2 ⟨hxQ, hxcut⟩ ⟨hyQ, hycut⟩ hopen'
  have hzero : ε • (x - u) = 0 := by
    calc
      ε • (x - u) = x' - u := by dsimp [x']; module
      _ = 0 := sub_eq_zero.mpr hxu
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left hε.ne')


end HirschCut
end


-- BEGIN Solutions/PolynomialAdjEndpoints.lean

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 2000000

noncomputable section

namespace HirschPolynomialAccess

variable {d : ℕ}

/-- Both endpoints of an `Adj` edge are extreme points of the parent set.
`Adj` stores that the whole segment is an extreme subset; the endpoint fact is
an elementary consequence. -/
lemma adj_right_extreme
    (P : Set (EuclideanSpace ℝ (Fin d)))
    {u z : EuclideanSpace ℝ (Fin d)}
    (hadj : Adj P u z) : z ∈ extremePoints ℝ P := by
  rcases hadj with ⟨huz, hseg⟩
  have hzP : z ∈ P := hseg.subset (right_mem_segment ℝ u z)
  refine ⟨hzP, ?_⟩
  intro x hxP y hyP hzopen
  have hxseg : x ∈ segment ℝ u z :=
    hseg.left_mem_of_mem_openSegment hxP hyP (right_mem_segment ℝ u z) hzopen
  have hyseg : y ∈ segment ℝ u z :=
    hseg.right_mem_of_mem_openSegment hxP hyP (right_mem_segment ℝ u z) hzopen
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hxseg
  obtain ⟨c, e, hc, he, hce, hy⟩ := hyseg
  obtain ⟨s, t, hs, ht, hst, hxy⟩ := hzopen
  have hcoeff : s * a + t * c + (s * b + t * e) = 1 := by
    calc
      s * a + t * c + (s * b + t * e) = s * (a + b) + t * (c + e) := by ring
      _ = s * 1 + t * 1 := by rw [hab, hce]
      _ = 1 := by linarith
  have hlin0 : s • x + t • y - z = 0 := sub_eq_zero.mpr hxy
  rw [← hx, ← hy] at hlin0
  have hrewrite :
      s • (a • u + b • z) + t • (c • u + e • z) - z =
        (s * a + t * c) • u + (s * b + t * e - 1) • z := by
    module
  have hlin1 :
      (s * a + t * c) • u + (s * b + t * e - 1) • z = 0 := by
    rw [← hrewrite]
    exact hlin0
  have hB : s * b + t * e - 1 = -(s * a + t * c) := by
    linarith [hcoeff]
  rw [hB] at hlin1
  have hlin : (s * a + t * c) • (u - z) = 0 := by
    rw [smul_sub, sub_eq_add_neg]
    simpa only [neg_smul] using hlin1
  have hcoef : s * a + t * c = 0 :=
    (smul_eq_zero.mp hlin).resolve_right (sub_ne_zero.mpr huz)
  have ha0 : a = 0 := by
    nlinarith [mul_nonneg ht.le hc]
  have hb1 : b = 1 := by linarith [hab]
  rw [ha0, zero_smul, zero_add, hb1, one_smul] at hx
  exact hx.symm

lemma adj_symm
    (P : Set (EuclideanSpace ℝ (Fin d)))
    {x y : EuclideanSpace ℝ (Fin d)}
    (h : Adj P x y) : Adj P y x := by
  refine ⟨h.1.symm, ?_⟩
  simpa [segment_symm] using h.2

lemma adj_left_extreme
    (P : Set (EuclideanSpace ℝ (Fin d)))
    {x y : EuclideanSpace ℝ (Fin d)}
    (h : Adj P x y) : x ∈ extremePoints ℝ P :=
  adj_right_extreme P (adj_symm P h)

end HirschPolynomialAccess
end


-- BEGIN Solutions/PolynomialHalfspaceAccessSubmission.lean

open scoped RealInnerProductSpace
open Set Hirsch HirschCut

set_option maxHeartbeats 4000000

noncomputable section

/-- From a retained original vertex, stop an outer edge walk at its first
cut-plane crossing. This helper does not require convexity of the outer set. -/
theorem HirschCut.outer_vertex_cut_access
    (d B : ℕ) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ Q) (hule : ⟪c, u⟫ ≤ b)
    (hv : v ∈ extremePoints ℝ Q) (hvge : b ≤ ⟪c, v⟫)
    (hD : DiamLE Q B) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}) ∧ ⟪c, z⟫ = b ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w B = z ∧
        ∀ j < B, w j = w (j + 1) ∨
          Adj (Q ∩ {x | ⟪c, x⟫ ≤ b}) (w j) (w (j + 1)) := by
  classical
  let P := Q ∩ {x | ⟪c, x⟫ ≤ b}
  by_cases huEq : ⟪c, u⟫ = b
  · have huP : u ∈ extremePoints ℝ P := by
      refine ⟨⟨hu.1, hule⟩, ?_⟩
      intro x hx y hy hop
      exact hu.2 hx.1 hy.1 hop
    exact ⟨u, huP, huEq, fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩
  have huLt : ⟪c, u⟫ < b := lt_of_le_of_ne hule huEq
  obtain ⟨w, hw0, hwB, hws⟩ := hD u hu v hv
  have hex : ∃ k : ℕ, k ≤ B ∧ b ≤ ⟪c, w k⟫ := by
    exact ⟨B, le_rfl, by simpa only [hwB] using hvge⟩
  let k := Nat.find hex
  have hk : k ≤ B ∧ b ≤ ⟪c, w k⟫ := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hzero
    have h := hk.2
    rw [hzero, hw0] at h
    linarith
  obtain ⟨j, hjk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hjB : j < B := by omega
  have hbefore (l : ℕ) (hl : l < k) : ⟪c, w l⟫ < b := by
    by_contra hnot
    have hge : b ≤ ⟪c, w l⟫ := le_of_not_gt hnot
    have hmin : k ≤ l := Nat.find_min' hex ⟨by omega, hge⟩
    omega
  have hleft : ⟪c, w j⟫ < b := hbefore j (by omega)
  have hright : b ≤ ⟪c, w (j + 1)⟫ := by
    simpa only [hjk, Nat.succ_eq_add_one] using hk.2
  have hedge : Adj Q (w j) (w (j + 1)) := by
    rcases hws j hjB with hsame | hedge
    · rw [hsame] at hleft
      exact False.elim ((not_lt_of_ge hright) hleft)
    · exact hedge
  obtain ⟨z, hcz, hzedge⟩ := clip_crossing_edge Q c b hedge hleft hright
  have hzext := HirschPolynomialAccess.adj_right_extreme P hzedge
  let wp : ℕ → EuclideanSpace ℝ (Fin d) := fun l => if l ≤ j then w l else z
  refine ⟨z, hzext, hcz, wp, ?_, ?_, ?_⟩
  · change (if 0 ≤ j then w 0 else z) = u
    rw [if_pos (Nat.zero_le j)]
    exact hw0
  · change (if B ≤ j then w B else z) = z
    exact if_neg (by omega)
  · intro l hlB
    by_cases hlj : l < j
    · have hl0 : l ≤ j := by omega
      have hl1 : l + 1 ≤ j := by omega
      have hpl : ⟪c, w l⟫ ≤ b := (hbefore l (by omega)).le
      have hpl1 : ⟪c, w (l + 1)⟫ ≤ b := (hbefore (l + 1) (by omega)).le
      rcases hws l hlB with hsame | hadj
      · exact Or.inl (by simpa only [wp, if_pos hl0, if_pos hl1] using hsame)
      · have he := retained_edge Q c b hadj hpl hpl1
        exact Or.inr (by simpa only [wp, if_pos hl0, if_pos hl1] using he)
    · by_cases hleq : l = j
      · subst l
        have hnext : ¬ j + 1 ≤ j := by omega
        exact Or.inr (by simpa only [wp, if_pos le_rfl, if_neg hnext] using hzedge)
      · have h0 : ¬ l ≤ j := by omega
        have h1 : ¬ l + 1 ≤ j := by omega
        exact Or.inl (by simp only [wp, if_neg h0, if_neg h1])

/-- Every vertex of a halfspace-clipped convex set reaches the specified cut
plane within the outer diameter budget. Vertices newly created by the cut
are already on the target plane; a vertex strictly inside is an original
outer vertex. This is cut-face access, not a bound on the full cut diameter. -/
theorem solution
    (d B : ℕ) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hconv : Convex ℝ Q)
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (u : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}))
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ Q) (hvge : b ≤ ⟪c, v⟫)
    (hD : DiamLE Q B) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}) ∧ ⟪c, z⟫ = b ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w B = z ∧
        ∀ j < B, w j = w (j + 1) ∨
          Adj (Q ∩ {x | ⟪c, x⟫ ≤ b}) (w j) (w (j + 1)) := by
  by_cases huEq : ⟪c, u⟫ = b
  · exact ⟨u, hu, huEq, fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩
  have huLt : ⟪c, u⟫ < b := lt_of_le_of_ne hu.1.2 huEq
  have huQ := strict_cut_extreme_to_parent Q hconv c b hu huLt
  exact outer_vertex_cut_access d B Q c b u v huQ hu.1.2 hv hvge hD

end


#print axioms solution
