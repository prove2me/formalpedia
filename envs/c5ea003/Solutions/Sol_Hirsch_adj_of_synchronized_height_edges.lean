-- Prove2me | solution 1 for Hirsch.adj_of_synchronized_height_edges
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T08:57:23.731969+00:00
-- url     : https://prove2.me/submissions/37aef322-49a8-49da-a43f-7188060f5892

import Definitions.Def_Hirsch_scalar_fiber_model
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

set_option autoImplicit false
set_option maxHeartbeats 8000000
open Set Hirsch AffineMap
open scoped Classical

noncomputable section

def edgeParam (H0 H1 H : ℝ) : ℝ :=
  if H0 = H1 then 0 else (H0 - H) / (H0 - H1)

theorem height_lineMap {E : Type*} [AddCommGroup E] [Module ℝ E]
    (hh : E →ᵃ[ℝ] ℝ) (a b : E) (t : ℝ) :
    hh (lineMap a b t) = (1 - t) * hh a + t * hh b := by
  simpa [lineMap_apply_ring] using apply_lineMap hh a b t

theorem height_interp {E : Type*} [AddCommGroup E] [Module ℝ E]
    (hh : E →ᵃ[ℝ] ℝ) (a b : E) (H0 H1 H : ℝ)
    (ha : hh a = H0) (hb : hh b = H1) (hne : H0 ≠ H1) :
    hh (lineMap a b (edgeParam H0 H1 H)) = H := by
  rw [height_lineMap, ha, hb]
  dsimp [edgeParam]
  rw [if_neg hne]
  field_simp [sub_ne_zero.mpr hne]
  ring

theorem edgeParam_nonneg {H0 H1 H : ℝ} (hH : H ≤ H0) (hlt : H1 < H0) :
    0 ≤ edgeParam H0 H1 H := by
  dsimp [edgeParam]
  rw [if_neg (ne_of_gt hlt)]
  exact div_nonneg (sub_nonneg.mpr hH) (sub_nonneg.mpr (le_of_lt hlt))

theorem edgeParam_le_one {H0 H1 H : ℝ} (hH : H1 ≤ H) (hlt : H1 < H0) :
    edgeParam H0 H1 H ≤ 1 := by
  dsimp [edgeParam]
  rw [if_neg (ne_of_gt hlt)]
  exact (div_le_one (sub_pos.mpr hlt)).mpr (sub_le_sub_left hH H0)

theorem mem_openSegment_pi {k : ℕ} {G : Type*} [AddCommGroup G] [Module ℝ G]
    {x y z : Fin k → G} (hz : z ∈ openSegment ℝ x y) (i : Fin k) :
    z i ∈ openSegment ℝ (x i) (y i) := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hz
  exact ⟨α, β, hα, hβ, hαβ, by simp [Pi.add_apply, Pi.smul_apply]⟩

theorem mem_segment_pi {k : ℕ} {G : Type*} [AddCommGroup G] [Module ℝ G]
    {x y z : Fin k → G} (hz : z ∈ segment ℝ x y) (i : Fin k) :
    z i ∈ segment ℝ (x i) (y i) := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hz
  exact ⟨α, β, hα, hβ, hαβ, by simp [Pi.add_apply, Pi.smul_apply]⟩

theorem eq_lineMap_of_mem_segment {G : Type*} [AddCommGroup G] [Module ℝ G]
    {p q z : G} (hz : z ∈ segment ℝ p q) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = lineMap p q t := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hz
  refine ⟨β, hβ, ?_, ?_⟩
  · linarith
  · have : α = 1 - β := by linarith
    subst this
    simp [lineMap_apply_module]

theorem unique_height_on_segment {G : Type*} [AddCommGroup G] [Module ℝ G]
    (hh : G →ᵃ[ℝ] ℝ) {p q z1 z2 : G}
    (hz1 : z1 ∈ segment ℝ p q) (hz2 : z2 ∈ segment ℝ p q)
    (hne : hh p ≠ hh q) (heq : hh z1 = hh z2) : z1 = z2 := by
  obtain ⟨t1, ht10, ht11, rfl⟩ := eq_lineMap_of_mem_segment hz1
  obtain ⟨t2, ht20, ht21, rfl⟩ := eq_lineMap_of_mem_segment hz2
  have h1 := height_lineMap hh p q t1
  have h2 := height_lineMap hh p q t2
  have : (1 - t1) * hh p + t1 * hh q = (1 - t2) * hh p + t2 * hh q := by
    simpa [h1, h2] using heq
  have : (t1 - t2) * (hh q - hh p) = 0 := by linarith
  have hne' : hh q - hh p ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have ht : t1 = t2 := sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne')
  simp [ht]

/-- Synchronized interpolation along genuine factor edges, with a tight
upper endpoint and a tight lower endpoint, is an edge of the fiber. -/
theorem solution {k d : ℕ}
    (P : Fin k → Set (EuclideanSpace ℝ (Fin d)))
    (hh : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ)
    (a b p q : Fin k → EuclideanSpace ℝ (Fin d))
    (H0 H1 : ℝ) (hlt : H1 < H0)
    (haH : ∀ i, hh i (a i) = H0)
    (hbH : ∀ i, hh i (b i) = H1)
    (hedge : ∀ i, Adj (P i) (p i) (q i))
    (haOn : ∀ i, a i ∈ segment ℝ (p i) (q i))
    (hbOn : ∀ i, b i ∈ segment ℝ (p i) (q i))
    (hpH : ∀ i, hh i (p i) ≥ H0)
    (hqH : ∀ i, hh i (q i) ≤ H1)
    (htight0 : ∃ i, hh i (p i) = H0)
    (htight1 : ∃ i, hh i (q i) = H1) :
    Adj (ScalarHeightFiber P hh) a b := by
  have hne : a ≠ b := by
    intro hab
    obtain ⟨i, _⟩ := htight0
    have : H0 = H1 := (haH i).symm.trans (by simpa [hab] using hbH i)
    linarith
  refine ⟨hne, ?_, ?_⟩
  · intro z hz
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hz
    refine ⟨?_, ?_⟩
    · intro i
      have hai := (hedge i).2.1 (haOn i)
      have hbi := (hedge i).2.1 (hbOn i)
      have : α • a i + β • b i ∈ segment ℝ (a i) (b i) :=
        ⟨α, β, hα, hβ, hαβ, rfl⟩
      have hseg : segment ℝ (a i) (b i) ⊆ segment ℝ (p i) (q i) := by
        intro x hx
        exact Convex.segment_subset (convex_segment _ _) (haOn i) (hbOn i) hx
      exact (hedge i).2.1 (hseg this)
    · intro i j
      have hαeq : α = 1 - β := by linarith
      have hzi : hh i ((α • a + β • b) i) = α * H0 + β * H1 := by
        have hx : (α • a + β • b) i = lineMap (a i) (b i) β := by
          rw [hαeq]
          simp [Pi.add_apply, Pi.smul_apply, lineMap_apply_module]
        rw [hx, height_lineMap, haH, hbH]
        simp [hαeq]
      have hzj : hh j ((α • a + β • b) j) = α * H0 + β * H1 := by
        have hx : (α • a + β • b) j = lineMap (a j) (b j) β := by
          rw [hαeq]
          simp [Pi.add_apply, Pi.smul_apply, lineMap_apply_module]
        rw [hx, height_lineMap, haH, hbH]
        simp [hαeq]
      exact hzi.trans hzj.symm
  · intro x hxF y hyF z hz hzopen
    have hzseg := hz
    obtain ⟨i0, hi0⟩ := htight0
    obtain ⟨i1, hi1⟩ := htight1
    have hx_on : ∀ i, x i ∈ segment ℝ (p i) (q i) := by
      intro i
      have hzopen_i := mem_openSegment_pi (k := k) hzopen i
      have hz_i := mem_segment_pi (k := k) hzseg i
      have hzi_on : z i ∈ segment ℝ (p i) (q i) :=
        Convex.segment_subset (convex_segment _ _) (haOn i) (hbOn i) hz_i
      exact (hedge i).2.left_mem_of_mem_openSegment
        (hxF.1 i) (hyF.1 i) hzi_on hzopen_i
    have hHx : ∀ i, hh i (x i) = hh i0 (x i0) := fun i => hxF.2 i i0
    have hle0 : hh i0 (x i0) ≤ H0 := by
      obtain ⟨t, ht0, ht1, hxeq⟩ := eq_lineMap_of_mem_segment (hx_on i0)
      have : hh i0 (x i0) = (1 - t) * H0 + t * hh i0 (q i0) := by
        rw [hxeq, height_lineMap, hi0]
      nlinarith [hqH i0, hpH i0, ht0, ht1]
    have hge1 : H1 ≤ hh i0 (x i0) := by
      obtain ⟨t, ht0, ht1, hxeq⟩ := eq_lineMap_of_mem_segment (hx_on i1)
      have : hh i1 (x i1) = (1 - t) * hh i1 (p i1) + t * H1 := by
        rw [hxeq, height_lineMap, hi1]
      have : hh i1 (x i1) = hh i0 (x i0) := hHx i1
      nlinarith [hpH i1, hqH i1, ht0, ht1]
    let H := hh i0 (x i0)
    have ht0 : 0 ≤ edgeParam H0 H1 H := edgeParam_nonneg hle0 hlt
    have ht1 : edgeParam H0 H1 H ≤ 1 := edgeParam_le_one hge1 hlt
    have hxeq : x = lineMap a b (edgeParam H0 H1 H) := by
      funext i
      have hne_i : hh i (p i) ≠ hh i (q i) := by
        linarith [hpH i, hqH i]
      have hinterp_on : lineMap (a i) (b i) (edgeParam H0 H1 H) ∈
          segment ℝ (p i) (q i) :=
        Convex.segment_subset (convex_segment _ _) (haOn i) (hbOn i)
          ⟨1 - edgeParam H0 H1 H, edgeParam H0 H1 H, sub_nonneg.mpr ht1, ht0, by ring,
            by simp [lineMap_apply_module]⟩
      have hHt :
          hh i (lineMap (a i) (b i) (edgeParam H0 H1 H)) = H :=
        height_interp (hh i) (a i) (b i) H0 H1 H (haH i) (hbH i) (ne_of_gt hlt)
      have hxi : (lineMap a b (edgeParam H0 H1 H)) i =
          lineMap (a i) (b i) (edgeParam H0 H1 H) := by
        simp [lineMap_apply_module, Pi.add_apply, Pi.smul_apply, sub_smul]
      refine (unique_height_on_segment (hh i) (hx_on i) hinterp_on hne_i ?_).trans hxi.symm
      exact (hHx i).trans hHt.symm
    have : lineMap a b (edgeParam H0 H1 H) ∈ segment ℝ a b :=
      ⟨1 - edgeParam H0 H1 H, edgeParam H0 H1 H, sub_nonneg.mpr ht1, ht0, by ring,
        by simp [lineMap_apply_module]⟩
    simpa [hxeq] using this
