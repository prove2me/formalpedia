-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_neighbour_positive_common_point
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T18:10:24.113346+00:00
-- url     : https://prove2.me/submissions/d5178be0-0b8f-46bf-b7e7-3ef4bd8ac37b

import Definitions.Def_PartialMonitoringGame
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.Combination

open scoped BigOperators

namespace BanditAlgorithm

noncomputable section

private def dotLinP {d : ℕ} (r : Fin d → ℝ) : Module.Dual ℝ (Fin d → ℝ) where
  toFun u := ∑ i, r i * u i
  map_add' x y := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' t x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

private lemma dotLinP_apply {d : ℕ} (r u : Fin d → ℝ) :
    dotLinP r u = ∑ i, r i * u i := rfl

private lemma dotLinP_injective {d : ℕ} : Function.Injective (dotLinP (d := d)) := by
  classical
  intro r s hrs
  funext i
  have h := LinearMap.congr_fun hrs (Pi.single i 1)
  simpa [dotLinP_apply, Pi.single_apply] using h

private lemma mem_annihilator_direction_of_constantP
    {d : ℕ} {S : Set (Fin d → ℝ)} (p : Fin d → ℝ) (hp : p ∈ S)
    (f : Module.Dual ℝ (Fin d → ℝ))
    (hf : ∀ x ∈ S, f x = f p) :
    f ∈ (affineSpan ℝ S).direction.dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro v hv
  rw [direction_affineSpan,
    vectorSpan_eq_span_vsub_set_right ℝ hp] at hv
  have hker : Submodule.span ℝ ((fun x => x -ᵥ p) '' S) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    change f (x - p) = 0
    rw [map_sub, hf x hx]
    simp
  exact hker hv

private lemma convex_pmCellP {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (a : Fin k) :
    Convex ℝ (pmCell G a) := by
  intro x hx y hy α β hα hβ hsum
  constructor
  · exact (convex_stdSimplex ℝ (Fin d)) hx.1 hy.1 hα hβ hsum
  · intro b
    have hxb := hx.2 b
    have hyb := hy.2 b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hid : (∑ i, (G.L a i - G.L b i) * (α * x i + β * y i)) =
        α * ∑ i, (G.L a i - G.L b i) * x i +
          β * ∑ i, (G.L a i - G.L b i) * y i := by
      calc
        _ = ∑ i, (α * ((G.L a i - G.L b i) * x i) +
            β * ((G.L a i - G.L b i) * y i)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    rw [hid]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hα hxb)
      (mul_nonpos_of_nonneg_of_nonpos hβ hyb)

private lemma cells_equal_of_loss_equalP
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    {a b : Fin k} (h : ∀ i, G.L a i = G.L b i) :
    pmCell G a = pmCell G b := by
  ext u
  constructor <;> intro hu
  · refine ⟨hu.1, ?_⟩
    intro c
    simpa only [h] using hu.2 c
  · refine ⟨hu.1, ?_⟩
    intro c
    simpa only [h] using hu.2 c

private lemma neighbour_loss_difference_ne_zeroP
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    {a b : Fin k} (hab : NeighbouringActions G a b) :
    dotLinP (fun i => G.L a i - G.L b i) ≠ 0 := by
  intro hzero
  have hrow : ∀ i, G.L a i = G.L b i := by
    intro i
    have hz : dotLinP (fun i => G.L a i - G.L b i) =
        dotLinP (fun _ : Fin d => (0 : ℝ)) := by
      rw [hzero]
      ext u
      simp [dotLinP_apply]
    have := congrFun (dotLinP_injective hz) i
    linarith
  have hcells := cells_equal_of_loss_equalP G hrow
  have hinter : pmCell G a ∩ pmCell G b = pmCell G a := by
    rw [hcells, Set.inter_self]
  unfold NeighbouringActions ParetoOptimalAction at hab
  rw [hinter] at hab
  omega

private lemma exists_pos_coord_of_full_simplex_affineDim
    {d : ℕ} {C : Set (Fin d → ℝ)} (hCne : C.Nonempty)
    (hCsimplex : C ⊆ stdSimplex ℝ (Fin d))
    (hCdim : affineDim C + 1 = d) (i : Fin d) :
    ∃ x ∈ C, 0 < x i := by
  classical
  by_contra hno
  push_neg at hno
  obtain ⟨p, hpC⟩ := hCne
  let D : Submodule ℝ (Fin d → ℝ) := (affineSpan ℝ C).direction
  let one : Module.Dual ℝ (Fin d → ℝ) := dotLinP (fun _ => 1)
  let coord : Module.Dual ℝ (Fin d → ℝ) := LinearMap.proj i
  have hzero : ∀ x ∈ C, x i = 0 := by
    intro x hx
    have hx0 := (hCsimplex hx).1 i
    exact le_antisymm (hno x hx) hx0
  have hone_ann : one ∈ D.dualAnnihilator := by
    apply mem_annihilator_direction_of_constantP p hpC
    intro x hx
    change (∑ j, (1 : ℝ) * x j) = ∑ j, (1 : ℝ) * p j
    simpa only [one_mul] using (hCsimplex hx).2.trans (hCsimplex hpC).2.symm
  have hcoord_ann : coord ∈ D.dualAnnihilator := by
    apply mem_annihilator_direction_of_constantP p hpC
    intro x hx
    change x i = p i
    rw [hzero x hx, hzero p hpC]
  have hone_p : one p = 1 := by
    change (∑ j, (1 : ℝ) * p j) = 1
    simpa only [one_mul] using (hCsimplex hpC).2
  have hcoord_p : coord p = 0 := hzero p hpC
  have hone_ne : one ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h p
    simp [hone_p] at this
  let pair : Fin 2 → Module.Dual ℝ (Fin d → ℝ) := ![one, coord]
  have hpair_li : LinearIndependent ℝ pair := by
    rw [LinearIndependent.pair_iff' hone_ne]
    intro t htc
    have hev := LinearMap.congr_fun htc p
    have ht : t = 0 := by
      simpa [hone_p, hcoord_p] using hev
    subst t
    have hcoord_ne : coord ≠ 0 := by
      intro h
      have hev := LinearMap.congr_fun h (Pi.single i 1)
      simpa [coord, Pi.single_apply] using hev
    apply hcoord_ne
    simpa using htc.symm
  let P : Submodule ℝ (Module.Dual ℝ (Fin d → ℝ)) :=
    Submodule.span ℝ (Set.range pair)
  have hPdim : Module.finrank ℝ P = 2 := by
    change Module.finrank ℝ (Submodule.span ℝ (Set.range pair)) = 2
    rw [finrank_span_eq_card hpair_li]
    simp
  have hPle : P ≤ D.dualAnnihilator := by
    rw [Submodule.span_le]
    rintro z ⟨j, rfl⟩
    fin_cases j
    · exact hone_ann
    · exact hcoord_ann
  have hDdim : Module.finrank ℝ D + 1 = d := by
    simpa [D, affineDim] using hCdim
  have hAnndim : Module.finrank ℝ D.dualAnnihilator = 1 := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq D
    have hV : Module.finrank ℝ (Fin d → ℝ) = d := by simp
    rw [hV] at h
    omega
  have hmono := Submodule.finrank_mono hPle
  rw [hPdim, hAnndim] at hmono
  omega

end

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    (a b : Fin k) (hab : NeighbouringActions G a b) :
    ∃ u : Fin d → ℝ, u ∈ pmCell G a ∩ pmCell G b ∧
      ∀ i : Fin d, 0 < u i := by
  classical
  let S : Set (Fin d → ℝ) := pmCell G a ∩ pmCell G b
  by_cases hex : ∃ u : Fin d → ℝ, u ∈ S ∧ ∀ i : Fin d, 0 < u i
  · simpa [S] using hex
  exfalso
  have hd : 0 < d := by
    have hdim := hab.2.2.2
    omega
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hcoord : ∃ i : Fin d, ∀ u ∈ S, u i = 0 := by
    by_contra hnone
    push_neg at hnone
    choose z hzS hz_ne using hnone
    let w : ℝ := (d : ℝ)⁻¹
    let u : Fin d → ℝ := ∑ j : Fin d, w • z j
    have hw : 0 < w := by
      exact inv_pos.mpr (by exact_mod_cast hd)
    have hconvS : Convex ℝ S :=
      (convex_pmCellP G a).inter (convex_pmCellP G b)
    have huS : u ∈ S := by
      apply hconvS.sum_mem
      · intro j hj
        exact hw.le
      · simp [w, hdR]
      · intro j hj
        exact hzS j
    have hu_pos : ∀ i : Fin d, 0 < u i := by
      intro i
      have hnonneg : ∀ j : Fin d, 0 ≤ z j i := by
        intro j
        exact (hzS j).1.1.1 i
      have hzi : 0 < z i i :=
        lt_of_le_of_ne (hnonneg i) (Ne.symm (hz_ne i))
      change 0 < (∑ j : Fin d, w • z j) i
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_pos'
      · intro j hj
        exact mul_nonneg hw.le (hnonneg j)
      · exact ⟨i, Finset.mem_univ i, mul_pos hw hzi⟩
    exact hex ⟨u, huS, hu_pos⟩
  obtain ⟨i, hiS⟩ := hcoord
  obtain ⟨p, hpa, hpb⟩ := hab.2.2.1
  have hpS : p ∈ S := ⟨hpa, hpb⟩
  let D : Submodule ℝ (Fin d → ℝ) := (affineSpan ℝ S).direction
  let one : Module.Dual ℝ (Fin d → ℝ) := dotLinP (fun _ => 1)
  let f : Module.Dual ℝ (Fin d → ℝ) :=
    dotLinP (fun j => G.L a j - G.L b j)
  let coord : Module.Dual ℝ (Fin d → ℝ) := LinearMap.proj i
  have hone_ann : one ∈ D.dualAnnihilator := by
    apply mem_annihilator_direction_of_constantP p hpS
    intro x hx
    change (∑ j, (1 : ℝ) * x j) = ∑ j, (1 : ℝ) * p j
    simpa only [one_mul] using hx.1.1.2.trans hpS.1.1.2.symm
  have hf_ann : f ∈ D.dualAnnihilator := by
    apply mem_annihilator_direction_of_constantP p hpS
    intro x hx
    change (∑ j, (G.L a j - G.L b j) * x j) =
      ∑ j, (G.L a j - G.L b j) * p j
    have hx1 := hx.1.2 b
    have hx2 := hx.2.2 a
    have hp1 := hpS.1.2 b
    have hp2 := hpS.2.2 a
    have hz_x : (∑ j, (G.L a j - G.L b j) * x j) = 0 := by
      have hneg : (∑ j, (G.L b j - G.L a j) * x j) =
          -(∑ j, (G.L a j - G.L b j) * x j) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hneg] at hx2
      linarith
    have hz_p : (∑ j, (G.L a j - G.L b j) * p j) = 0 := by
      have hneg : (∑ j, (G.L b j - G.L a j) * p j) =
          -(∑ j, (G.L a j - G.L b j) * p j) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hneg] at hp2
      linarith
    rw [hz_x, hz_p]
  have hcoord_ann : coord ∈ D.dualAnnihilator := by
    apply mem_annihilator_direction_of_constantP p hpS
    intro x hx
    change x i = p i
    rw [hiS x hx, hiS p hpS]
  have hone_p : one p = 1 := by
    change (∑ j, (1 : ℝ) * p j) = 1
    simpa only [one_mul] using hpa.1.2
  have hf_p : f p = 0 := by
    change (∑ j, (G.L a j - G.L b j) * p j) = 0
    have hp1 := hpa.2 b
    have hp2 := hpb.2 a
    have hneg : (∑ j, (G.L b j - G.L a j) * p j) =
        -(∑ j, (G.L a j - G.L b j) * p j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hneg] at hp2
    linarith
  have hcoord_p : coord p = 0 := hiS p hpS
  have hf_ne : f ≠ 0 := neighbour_loss_difference_ne_zeroP G hab
  have hone_ne : one ≠ 0 := by
    intro h
    have hev := LinearMap.congr_fun h p
    simp [hone_p] at hev
  let pair : Fin 2 → Module.Dual ℝ (Fin d → ℝ) := ![one, f]
  have hpair_li : LinearIndependent ℝ pair := by
    rw [LinearIndependent.pair_iff' hone_ne]
    intro t htf
    have hev := LinearMap.congr_fun htf p
    have ht : t = 0 := by
      simpa [hone_p, hf_p] using hev
    subst t
    apply hf_ne
    simpa using htf.symm
  let P : Submodule ℝ (Module.Dual ℝ (Fin d → ℝ)) :=
    Submodule.span ℝ (Set.range pair)
  have hPdim : Module.finrank ℝ P = 2 := by
    change Module.finrank ℝ (Submodule.span ℝ (Set.range pair)) = 2
    rw [finrank_span_eq_card hpair_li]
    simp
  have hPle : P ≤ D.dualAnnihilator := by
    rw [Submodule.span_le]
    rintro z ⟨j, rfl⟩
    fin_cases j
    · exact hone_ann
    · exact hf_ann
  have hDdim : Module.finrank ℝ D + 2 = d := by
    simpa [D, S, affineDim] using hab.2.2.2
  have hAnndim : Module.finrank ℝ D.dualAnnihilator = 2 := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq D
    have hV : Module.finrank ℝ (Fin d → ℝ) = d := by simp
    rw [hV] at h
    omega
  have hPeq : P = D.dualAnnihilator :=
    Submodule.eq_of_le_of_finrank_eq hPle (hPdim.trans hAnndim.symm)
  have hcP : coord ∈ P := hPeq.symm ▸ hcoord_ann
  have hcspan : coord ∈
      Submodule.span ℝ ({one, f} : Set (Module.Dual ℝ (Fin d → ℝ))) := by
    simpa [P, pair, Matrix.cons_val_zero, Matrix.cons_val_one, Set.pair_comm] using hcP
  rw [Submodule.mem_span_pair] at hcspan
  obtain ⟨r, s, hrs⟩ := hcspan
  have hr : r = 0 := by
    have hev := LinearMap.congr_fun hrs p
    simp only [LinearMap.add_apply, LinearMap.smul_apply] at hev
    rw [hone_p, hf_p, hcoord_p] at hev
    simpa using hev
  subst r
  have hcf : coord = s • f := by
    simpa using hrs.symm

  obtain ⟨x, hxa, hxi⟩ := exists_pos_coord_of_full_simplex_affineDim
    hab.1.1 (fun _ hx => hx.1) hab.1.2 i
  have hfx_le : f x ≤ 0 := hxa.2 b
  have hfx_ne : f x ≠ 0 := by
    intro hfx
    have hxb : x ∈ pmCell G b := by
      refine ⟨hxa.1, ?_⟩
      intro z
      have haz := hxa.2 z
      have heq : (∑ j, (G.L b j - G.L z j) * x j) =
          (∑ j, (G.L a j - G.L z j) * x j) - f x := by
        rw [dotLinP_apply]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [heq, hfx]
      simpa using haz
    have hxzero := hiS x ⟨hxa, hxb⟩
    linarith
  have hfx : f x < 0 := lt_of_le_of_ne hfx_le hfx_ne

  obtain ⟨y, hyb, hyi⟩ := exists_pos_coord_of_full_simplex_affineDim
    hab.2.1.1 (fun _ hy => hy.1) hab.2.1.2 i
  have hfy_nonneg : 0 ≤ f y := by
    have hba := hyb.2 a
    change (∑ j, (G.L b j - G.L a j) * y j) ≤ 0 at hba
    have hneg : (∑ j, (G.L b j - G.L a j) * y j) = -f y := by
      rw [dotLinP_apply, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hneg] at hba
    linarith
  have hfy_ne : f y ≠ 0 := by
    intro hfy
    have hya : y ∈ pmCell G a := by
      refine ⟨hyb.1, ?_⟩
      intro z
      have hbz := hyb.2 z
      have heq : (∑ j, (G.L a j - G.L z j) * y j) =
          (∑ j, (G.L b j - G.L z j) * y j) + f y := by
        rw [dotLinP_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [heq, hfy]
      simpa using hbz
    have hyzero := hiS y ⟨hya, hyb⟩
    linarith
  have hfy : 0 < f y := lt_of_le_of_ne hfy_nonneg (Ne.symm hfy_ne)
  have hcx := LinearMap.congr_fun hcf x
  have hcy := LinearMap.congr_fun hcf y
  change x i = s * f x at hcx
  change y i = s * f y at hcy
  nlinarith
