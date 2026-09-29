-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_neighbour_loss_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T18:03:55.767748+00:00
-- url     : https://prove2.me/submissions/05af89b5-77b3-4fd6-82f0-97e3f104feb5

import Definitions.Def_PartialMonitoringGame
import Mathlib.LinearAlgebra.Dual.Lemmas

open scoped BigOperators

namespace BanditAlgorithm

noncomputable section

private def dotLin {d : ℕ} (r : Fin d → ℝ) : Module.Dual ℝ (Fin d → ℝ) where
  toFun u := ∑ i, r i * u i
  map_add' x y := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' t x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

private lemma dotLin_apply {d : ℕ} (r u : Fin d → ℝ) :
    dotLin r u = ∑ i, r i * u i := rfl

private lemma dotLin_injective {d : ℕ} : Function.Injective (dotLin (d := d)) := by
  classical
  intro r s hrs
  funext i
  have h := LinearMap.congr_fun hrs (Pi.single i 1)
  simpa [dotLin_apply, Pi.single_apply] using h

private lemma mem_annihilator_direction_of_constant
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

private lemma cell_pair_dot_eq_zero
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    {a b : Fin k} {u : Fin d → ℝ}
    (ha : u ∈ pmCell G a) (hb : u ∈ pmCell G b) :
    dotLin (fun i => G.L a i - G.L b i) u = 0 := by
  have hab := ha.2 b
  have hba := hb.2 a
  rw [dotLin_apply]
  have hneg : (∑ i, (G.L b i - G.L a i) * u i) =
      -(∑ i, (G.L a i - G.L b i) * u i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hneg] at hba
  linarith

private lemma cells_equal_of_loss_equal
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

private lemma neighbour_loss_difference_ne_zero
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    {a b : Fin k} (hab : NeighbouringActions G a b) :
    dotLin (fun i => G.L a i - G.L b i) ≠ 0 := by
  intro hzero
  have hrow : ∀ i, G.L a i = G.L b i := by
    intro i
    have hz : dotLin (fun i => G.L a i - G.L b i) =
        dotLin (fun _ : Fin d => (0 : ℝ)) := by
      rw [hzero]
      ext u
      simp [dotLin_apply]
    have := congrFun (dotLin_injective hz) i
    linarith
  have hcells := cells_equal_of_loss_equal G hrow
  have hinter : pmCell G a ∩ pmCell G b = pmCell G a := by
    rw [hcells, Set.inter_self]
  unfold NeighbouringActions ParetoOptimalAction at hab
  rw [hinter] at hab
  omega

end

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    (a b : Fin k) (hab : NeighbouringActions G a b) :
    ∀ c : Fin k, c ∈ pmNeighbourhood G a b →
      ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
        ∀ i : Fin d, G.L c i = α * G.L a i + (1 - α) * G.L b i := by
  classical
  intro c hc
  let S : Set (Fin d → ℝ) := pmCell G a ∩ pmCell G b
  let D : Submodule ℝ (Fin d → ℝ) := (affineSpan ℝ S).direction
  let one : Module.Dual ℝ (Fin d → ℝ) := dotLin (fun _ => 1)
  let f : Module.Dual ℝ (Fin d → ℝ) :=
    dotLin (fun i => G.L a i - G.L b i)
  let g : Module.Dual ℝ (Fin d → ℝ) :=
    dotLin (fun i => G.L a i - G.L c i)

  obtain ⟨p, hpa, hpb⟩ := hab.2.2.1
  have hpS : p ∈ S := ⟨hpa, hpb⟩
  have hpc : p ∈ pmCell G c := hc hpS

  have hone_ann : one ∈ D.dualAnnihilator := by
    apply mem_annihilator_direction_of_constant p hpS
    intro x hx
    change (∑ i, (1 : ℝ) * x i) = ∑ i, (1 : ℝ) * p i
    simpa only [one_mul] using hx.1.1.2.trans hpS.1.1.2.symm
  have hf_ann : f ∈ D.dualAnnihilator := by
    apply mem_annihilator_direction_of_constant p hpS
    intro x hx
    change dotLin (fun i => G.L a i - G.L b i) x =
      dotLin (fun i => G.L a i - G.L b i) p
    rw [cell_pair_dot_eq_zero G hx.1 hx.2,
      cell_pair_dot_eq_zero G hpS.1 hpS.2]
  have hg_ann : g ∈ D.dualAnnihilator := by
    apply mem_annihilator_direction_of_constant p hpS
    intro x hx
    have hxc : x ∈ pmCell G c := hc hx
    change dotLin (fun i => G.L a i - G.L c i) x =
      dotLin (fun i => G.L a i - G.L c i) p
    rw [cell_pair_dot_eq_zero G hx.1 hxc,
      cell_pair_dot_eq_zero G hpa hpc]

  have hone_p : one p = 1 := by
    change (∑ i, (1 : ℝ) * p i) = 1
    simpa only [one_mul] using hpa.1.2
  have hf_p : f p = 0 := by
    exact cell_pair_dot_eq_zero G hpa hpb
  have hg_p : g p = 0 := by
    exact cell_pair_dot_eq_zero G hpa hpc
  have hf_ne : f ≠ 0 := by
    exact neighbour_loss_difference_ne_zero G hab
  have hone_ne : one ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h p
    simp [hone_p] at this

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
  have hP_dim : Module.finrank ℝ P = 2 := by
    change Module.finrank ℝ (Submodule.span ℝ (Set.range pair)) = 2
    rw [finrank_span_eq_card hpair_li]
    simp
  have hP_le : P ≤ D.dualAnnihilator := by
    rw [Submodule.span_le]
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact hone_ann
    · exact hf_ann
  have hD_dim : Module.finrank ℝ D + 2 = d := by
    simpa [D, S, affineDim] using hab.2.2.2
  have hAnn_dim : Module.finrank ℝ D.dualAnnihilator = 2 := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq D
    have hV : Module.finrank ℝ (Fin d → ℝ) = d := by simp
    rw [hV] at h
    omega
  have hP_eq : P = D.dualAnnihilator :=
    Submodule.eq_of_le_of_finrank_eq hP_le (hP_dim.trans hAnn_dim.symm)
  have hgP : g ∈ P := hP_eq.symm ▸ hg_ann
  have hg_span : g ∈ Submodule.span ℝ ({one, f} : Set (Module.Dual ℝ (Fin d → ℝ))) := by
    simpa [P, pair, Matrix.cons_val_zero, Matrix.cons_val_one, Set.pair_comm] using hgP
  rw [Submodule.mem_span_pair] at hg_span
  obtain ⟨r, s, hrs⟩ := hg_span
  have hr : r = 0 := by
    have hev := LinearMap.congr_fun hrs p
    simp only [LinearMap.add_apply, LinearMap.smul_apply] at hev
    rw [hone_p, hf_p, hg_p] at hev
    simpa using hev
  subst r
  have hgf : g = s • f := by
    simpa using hrs.symm
  have hrow : ∀ i : Fin d,
      G.L a i - G.L c i = s * (G.L a i - G.L b i) := by
    intro i
    have hev := LinearMap.congr_fun hgf (Pi.single i 1)
    simpa [g, f, dotLin_apply, Pi.single_apply] using hev

  have hnot_ab : ¬ pmCell G a ⊆ pmCell G b := by
    intro hsub
    have hinter : pmCell G a ∩ pmCell G b = pmCell G a := Set.inter_eq_left.mpr hsub
    have hPareto := hab.1.2
    have hEdge := hab.2.2.2
    rw [hinter] at hEdge
    omega
  obtain ⟨x, hxa, hxnb⟩ := Set.not_subset.mp hnot_ab
  have hfx_le : f x ≤ 0 := hxa.2 b
  have hfx_ne : f x ≠ 0 := by
    intro hfx
    apply hxnb
    refine ⟨hxa.1, ?_⟩
    intro z
    have haz := hxa.2 z
    have heq : (∑ i, (G.L b i - G.L z i) * x i) =
        (∑ i, (G.L a i - G.L z i) * x i) - f x := by
      rw [dotLin_apply]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq, hfx]
    simpa using haz
  have hfx : f x < 0 := lt_of_le_of_ne hfx_le hfx_ne

  have hnot_ba : ¬ pmCell G b ⊆ pmCell G a := by
    intro hsub
    have hinter : pmCell G a ∩ pmCell G b = pmCell G b := Set.inter_eq_right.mpr hsub
    have hPareto := hab.2.1.2
    have hEdge := hab.2.2.2
    rw [hinter] at hEdge
    omega
  obtain ⟨y, hyb, hyna⟩ := Set.not_subset.mp hnot_ba
  have hfy_nonneg : 0 ≤ f y := by
    have hba := hyb.2 a
    change (∑ i, (G.L b i - G.L a i) * y i) ≤ 0 at hba
    have hneg : (∑ i, (G.L b i - G.L a i) * y i) = -f y := by
      rw [dotLin_apply, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg] at hba
    linarith
  have hfy_ne : f y ≠ 0 := by
    intro hfy
    apply hyna
    refine ⟨hyb.1, ?_⟩
    intro z
    have hbz := hyb.2 z
    have heq : (∑ i, (G.L a i - G.L z i) * y i) =
        (∑ i, (G.L b i - G.L z i) * y i) + f y := by
      rw [dotLin_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq, hfy]
    simpa using hbz
  have hfy : 0 < f y := lt_of_le_of_ne hfy_nonneg (Ne.symm hfy_ne)

  have hs_nonneg : 0 ≤ s := by
    have hac := hxa.2 c
    have heval : g x = s * f x := by
      rw [hgf]
      rfl
    change g x ≤ 0 at hac
    rw [heval] at hac
    nlinarith
  have hs_le : s ≤ 1 := by
    have hbc := hyb.2 c
    have heq : (∑ i, (G.L b i - G.L c i) * y i) = (s - 1) * f y := by
      rw [dotLin_apply]
      calc
        (∑ i, (G.L b i - G.L c i) * y i) =
            (∑ i, ((G.L a i - G.L c i) - (G.L a i - G.L b i)) * y i) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = (∑ i, (s * (G.L a i - G.L b i) -
              (G.L a i - G.L b i)) * y i) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hrow i]
        _ = (s - 1) * f y := by
              rw [dotLin_apply]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
    rw [heq] at hbc
    nlinarith

  refine ⟨1 - s, by linarith, by linarith, ?_⟩
  intro i
  have := hrow i
  ring_nf at this ⊢
  linarith
