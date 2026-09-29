-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_exists_unit_affine_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T17:50:09.30459+00:00
-- url     : https://prove2.me/submissions/3d9bc672-0377-435c-bbaf-eea856b34a47

import Definitions.Def_PartialMonitoringGame

open scoped BigOperators

namespace BanditAlgorithm

noncomputable section

theorem _root_.solution {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) :
    ∃ G' : PartialMonitoringGame k d 𝕊, ∃ lam : ℝ, ∃ c : Fin d → ℝ,
      0 < lam ∧
      (∀ a i, G'.L a i ∈ Set.Icc (0 : ℝ) 1) ∧
      (LocallyObservable G → LocallyObservable G') ∧
      (∀ a i, G'.L a i = lam * G.L a i + c i) ∧
      G'.Φ = G.Φ := by
  classical
  let T : ℝ := ∑ a : Fin k, ∑ i : Fin d, |G.L a i|
  let K : ℝ := T + 1
  have hT : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro a ha
    exact Finset.sum_nonneg fun i hi => abs_nonneg _
  have hK : 0 < K := by dsimp [K]; linarith
  let lam : ℝ := 1 / (2 * K)
  let c : Fin d → ℝ := fun _ => 1 / 2
  let G' : PartialMonitoringGame k d 𝕊 := {
    L := fun a i => lam * G.L a i + c i
    Φ := G.Φ }
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have habs (a : Fin k) (i : Fin d) : |G.L a i| ≤ T := by
    dsimp [T]
    calc
      |G.L a i| ≤ ∑ j : Fin d, |G.L a j| :=
        Finset.single_le_sum
          (f := fun j : Fin d => |G.L a j|)
          (fun j hj => abs_nonneg _) (Finset.mem_univ i)
      _ ≤ ∑ b : Fin k, ∑ j : Fin d, |G.L b j| :=
        Finset.single_le_sum
          (f := fun b : Fin k => ∑ j : Fin d, |G.L b j|)
          (fun b hb => Finset.sum_nonneg fun j hj => abs_nonneg _)
          (Finset.mem_univ a)
  have hunit (a : Fin k) (i : Fin d) : G'.L a i ∈ Set.Icc (0 : ℝ) 1 := by
    have hlo : -K ≤ G.L a i := by
      have := (abs_le.mp ((habs a i).trans (show T ≤ K by dsimp [K]; linarith))).1
      exact this
    have hhi : G.L a i ≤ K := by
      exact (abs_le.mp ((habs a i).trans (show T ≤ K by dsimp [K]; linarith))).2
    dsimp [G', lam, c]
    constructor
    · rw [show 1 / (2 * K) * G.L a i + 1 / 2 =
          (G.L a i + K) / (2 * K) by field_simp [hK.ne']]
      exact div_nonneg (by linarith) (by positivity)
    · rw [show 1 / (2 * K) * G.L a i + 1 / 2 =
          (G.L a i + K) / (2 * K) by field_simp [hK.ne']]
      rw [div_le_one (by positivity : 0 < 2 * K)]
      linarith
  have hcell (a : Fin k) : pmCell G' a = pmCell G a := by
    ext u
    simp only [pmCell, Set.mem_setOf_eq]
    constructor
    · intro hu
      refine ⟨hu.1, ?_⟩
      intro b
      have hh := hu.2 b
      dsimp [G', lam, c] at hh
      have heq :
          (∑ i, ((1 / (2 * K)) * G.L a i + 1 / 2 -
              ((1 / (2 * K)) * G.L b i + 1 / 2)) * u i) =
            (1 / (2 * K)) * ∑ i, (G.L a i - G.L b i) * u i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [heq] at hh
      apply le_of_not_gt
      intro hspos
      have hc : 0 < (1 / (2 * K)) *
          ∑ i, (G.L a i - G.L b i) * u i :=
        mul_pos (by positivity) hspos
      linarith
    · intro hu
      refine ⟨hu.1, ?_⟩
      intro b
      have hh := hu.2 b
      dsimp [G', lam, c]
      rw [show
          (∑ i, ((1 / (2 * K)) * G.L a i + 1 / 2 -
              ((1 / (2 * K)) * G.L b i + 1 / 2)) * u i) =
            (1 / (2 * K)) * ∑ i, (G.L a i - G.L b i) * u i by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring]
      exact mul_nonpos_of_nonneg_of_nonpos hlam.le hh
  have hneigh (a b : Fin k) : NeighbouringActions G' a b ↔ NeighbouringActions G a b := by
    simp only [NeighbouringActions, ParetoOptimalAction, hcell]
  have hN (a b : Fin k) : pmNeighbourhood G' a b = pmNeighbourhood G a b := by
    ext x
    simp only [pmNeighbourhood, Set.mem_setOf_eq, hcell]
  have hloc : LocallyObservable G → LocallyObservable G' := by
    intro h a b hab
    obtain ⟨f, hf, hsupp⟩ := h a b ((hneigh a b).mp hab)
    let f' : Fin k × 𝕊 → ℝ := fun x => lam * f x
    refine ⟨f', ?_, ?_⟩
    · intro i
      change (∑ x : Fin k, lam * f (x, G.Φ x i)) = _
      rw [← Finset.mul_sum, hf i]
      dsimp [G', lam, c]
      ring
    · intro x hx σ
      have hx' : x ∉ pmNeighbourhood G a b := by simpa [hN a b] using hx
      simp [f', hsupp x hx' σ]
  exact ⟨G', lam, c, hlam, hunit, hloc, fun _ _ => rfl, rfl⟩

end
end BanditAlgorithm
