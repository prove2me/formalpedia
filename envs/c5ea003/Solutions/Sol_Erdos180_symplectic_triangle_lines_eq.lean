-- Prove2me | solution 1 for Erdos180.symplectic_triangle_lines_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:34:25.541692+00:00
-- url     : https://prove2.me/submissions/6a49840d-8c34-43d9-a957-ae3f4fa35e79

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Theorems.Thm_Erdos180_symplecticLine_eq_of_points
import Theorems.Thm_Erdos180_symplecticPoint_sup_finrank

namespace Erdos180

noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

lemma symplectic_isotropic_finrank_le_two
    (S : Submodule K (SymplecticVector K))
    (hS : ∀ u ∈ S, ∀ v ∈ S,
      standardSymplecticForm K u v = 0) :
    Module.finrank K S ≤ 2 := by
  have hle : S ≤ (standardSymplecticBilin K).orthogonal S := by
    intro x hx
    change ∀ y ∈ S, standardSymplecticForm K y x = 0
    intro y hy
    exact hS y hy x hx
  have hrank := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal
    (standardSymplecticBilin_nondegenerate K)] at hrank
  have hambient : Module.finrank K (SymplecticVector K) = 4 := by
    simp [SymplecticVector]
  rw [hambient] at hrank
  omega

lemma symplectic_triangle_points_collinear
    {p q r : SymplecticPoint K} (hpq : p ≠ q)
    {Lpq Lpr Lqr : SymplecticLine K}
    (hpLpq : p.1 ≤ Lpq.1) (hqLpq : q.1 ≤ Lpq.1)
    (hpLpr : p.1 ≤ Lpr.1) (hrLpr : r.1 ≤ Lpr.1)
    (hqLqr : q.1 ≤ Lqr.1) (hrLqr : r.1 ≤ Lqr.1) :
    r.1 ≤ Lpq.1 := by
  let T : Submodule K (SymplecticVector K) :=
    (p.1 ⊔ q.1) ⊔ r.1
  have hiso : ∀ u ∈ T, ∀ v ∈ T,
      standardSymplecticForm K u v = 0 := by
    intro u hu v hv
    obtain ⟨ab, hab, c, hc, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hab
    obtain ⟨de, hde, f, hf, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨d, hd, e, he, rfl⟩ := Submodule.mem_sup.mp hde
    have had := Lpq.2.2 a (hpLpq ha) d (hpLpq hd)
    have hae := Lpq.2.2 a (hpLpq ha) e (hqLpq he)
    have haf := Lpr.2.2 a (hpLpr ha) f (hrLpr hf)
    have hbd := Lpq.2.2 b (hqLpq hb) d (hpLpq hd)
    have hbe := Lpq.2.2 b (hqLpq hb) e (hqLpq he)
    have hbf := Lqr.2.2 b (hqLqr hb) f (hrLqr hf)
    have hcd := Lpr.2.2 c (hrLpr hc) d (hpLpr hd)
    have hce := Lqr.2.2 c (hrLqr hc) e (hqLqr he)
    have hcf := Lpr.2.2 c (hrLpr hc) f (hrLpr hf)
    simp [standardSymplecticForm_add_left,
      standardSymplecticForm_add_right,
      had, hae, haf, hbd, hbe, hbf, hcd, hce, hcf]
  have hbound : Module.finrank K T ≤ 2 :=
    symplectic_isotropic_finrank_le_two K T hiso
  have hspan : p.1 ⊔ q.1 = T :=
    Submodule.eq_of_le_of_finrank_le le_sup_left
      (by simpa [symplecticPoint_sup_finrank K hpq] using hbound)
  exact (show r.1 ≤ T from le_sup_right).trans
    (hspan.symm ▸ sup_le hpLpq hqLpq)

end

end Erdos180

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    {p q r : SymplecticPoint K}
    (hpq : p ≠ q) (hqr : q ≠ r)
    {Lpq Lpr Lqr : SymplecticLine K}
    (hpLpq : p.1 ≤ Lpq.1) (hqLpq : q.1 ≤ Lpq.1)
    (hpLpr : p.1 ≤ Lpr.1) (hrLpr : r.1 ≤ Lpr.1)
    (hqLqr : q.1 ≤ Lqr.1) (hrLqr : r.1 ≤ Lqr.1) :
    Lpq = Lqr := by
  have hrLpq : r.1 ≤ Lpq.1 := symplectic_triangle_points_collinear K hpq
    hpLpq hqLpq hpLpr hrLpr hqLqr hrLqr
  exact symplecticLine_eq_of_points K hqr hqLpq hrLpq hqLqr hrLqr
