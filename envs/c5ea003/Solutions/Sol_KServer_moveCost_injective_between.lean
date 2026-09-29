-- Prove2me | solution 1 for KServer.moveCost_injective_between
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:20:42.183573+00:00
-- url     : https://prove2.me/submissions/f23683e3-052d-4b4d-9080-40464b1a353d

import Mathlib
import Definitions.Def_KServer_model

open KServer

private theorem mc_triangle {k : ℕ} {M : Type} [MetricSpace M]
    (A B C : Config k M) : moveCost A C ≤ moveCost A B + moveCost B C := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

private theorem sum_diff_single {k : ℕ} (F G : Fin k → ℝ) (p : Fin k)
    (h : ∀ i, i ≠ p → F i = G i) : ∑ i, F i - ∑ i, G i = F p - G p := by
  classical
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ p),
    ← Finset.add_sum_erase _ G (Finset.mem_univ p),
    Finset.sum_congr rfl (fun i hi => h i (Finset.ne_of_mem_erase hi))]
  ring

private theorem mc_to_update {k : ℕ} {M : Type} [MetricSpace M]
    (Y : Config k M) (j : Fin k) (v : M) :
    moveCost Y (Function.update Y j v) = dist (Y j) v := by
  classical
  have h := sum_diff_single (fun i => dist (Y i) (Function.update Y j v i))
    (fun _ => (0:ℝ)) j (fun i hi => by
      show dist (Y i) (Function.update Y j v i) = 0
      rw [Function.update_of_ne hi]; simp)
  simp only [Finset.sum_const_zero, sub_zero, Function.update_self] at h
  simpa [moveCost] using h

private theorem mc_update_left {k : ℕ} {M : Type} [MetricSpace M]
    (Y Z : Config k M) (j : Fin k) (v : M) :
    moveCost (Function.update Y j v) Z
      = moveCost Y Z - dist (Y j) (Z j) + dist v (Z j) := by
  classical
  have h := sum_diff_single (fun i => dist (Function.update Y j v i) (Z i))
    (fun i => dist (Y i) (Z i)) j (fun i hi => by
      show dist (Function.update Y j v i) (Z i) = dist (Y i) (Z i)
      rw [Function.update_of_ne hi])
  simp only [Function.update_self] at h
  have : moveCost (Function.update Y j v) Z - moveCost Y Z = dist v (Z j) - dist (Y j) (Z j) := h
  linarith

/-- **Injective reduction along a geodesic.**  If the target `Z` is injective, every
configuration covering `r` can be replaced by an injective one covering `r` that lies
between it and `Z`. -/
theorem solution (k : ℕ) (M : Type) [MetricSpace M]
    (Y Z : Config k M) (hZ : Function.Injective Z) (r : M) (hY : ∃ i, Y i = r) :
    ∃ Y' : Config k M, Function.Injective Y' ∧ (∃ i, Y' i = r) ∧
      moveCost Y Y' + moveCost Y' Z ≤ moveCost Y Z := by
  classical
  -- induct on the number of coordinates where `Y` differs from `Z`
  suffices H : ∀ n : ℕ, ∀ Y : Config k M,
      (Finset.univ.filter (fun i => Y i ≠ Z i)).card ≤ n → (∃ i, Y i = r) →
      ∃ Y' : Config k M, Function.Injective Y' ∧ (∃ i, Y' i = r) ∧
        moveCost Y Y' + moveCost Y' Z ≤ moveCost Y Z by
    exact H _ Y le_rfl hY
  intro n
  induction n with
  | zero =>
      intro Y hcard hYr
      have heq : Y = Z := by
        funext i
        by_contra hne
        have : i ∈ Finset.univ.filter (fun i => Y i ≠ Z i) := by
          simp [hne]
        have := Finset.card_pos.mpr ⟨i, this⟩
        omega
      subst heq
      exact ⟨Y, hZ, hYr, by simp [moveCost]⟩
  | succ n ih =>
      intro Y hcard hYr
      by_cases hinj : Function.Injective Y
      · exact ⟨Y, hinj, hYr, by simp [moveCost]⟩
      · -- two indices carry the same point; one of them differs from `Z`
        rw [Function.not_injective_iff] at hinj
        obtain ⟨a, b, hab, hne⟩ := hinj
        have hZab : Z a ≠ Z b := fun h => hne (hZ h)
        have hpick : (Y a ≠ Z a ∧ Y b = Y a) ∨ (Y b ≠ Z b ∧ Y a = Y b) := by
          by_cases hb : Y b = Z b
          · left
            refine ⟨fun ha => hZab ?_, hab.symm⟩
            rw [← ha, hab, hb]
          · right
            exact ⟨hb, hab⟩
        obtain ⟨j, i', hji, hjne, hi'⟩ :
            ∃ j i' : Fin k, j ≠ i' ∧ Y j ≠ Z j ∧ Y i' = Y j := by
          rcases hpick with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨a, b, hne, h1, h2⟩
          · exact ⟨b, a, Ne.symm hne, h1, h2⟩
        set Y₁ : Config k M := Function.update Y j (Z j) with hY₁
        have hY₁ne : ∀ i, i ≠ j → Y₁ i = Y i := fun i hi => Function.update_of_ne hi _ _
        have hY₁j : Y₁ j = Z j := Function.update_self _ _ _
        -- `Y₁` still covers `r`
        have hY₁r : ∃ i, Y₁ i = r := by
          obtain ⟨i₀, hi₀⟩ := hYr
          by_cases hij : i₀ = j
          · exact ⟨i', by rw [hY₁ne i' (Ne.symm hji), hi', ← hij, hi₀]⟩
          · exact ⟨i₀, by rw [hY₁ne i₀ hij, hi₀]⟩
        -- the differing set shrinks
        have hshrink : (Finset.univ.filter (fun i => Y₁ i ≠ Z i)).card + 1
            ≤ (Finset.univ.filter (fun i => Y i ≠ Z i)).card := by
          have hsub : Finset.univ.filter (fun i => Y₁ i ≠ Z i)
              ⊆ (Finset.univ.filter (fun i => Y i ≠ Z i)).erase j := by
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            have hij : i ≠ j := by
              rintro rfl; exact hi hY₁j
            rw [hY₁ne i hij] at hi
            exact Finset.mem_erase.mpr ⟨hij, by simp [hi]⟩
          have hjmem : j ∈ Finset.univ.filter (fun i => Y i ≠ Z i) := by simp [hjne]
          have := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem hjmem] at this
          have hpos := Finset.card_pos.mpr ⟨j, hjmem⟩
          omega
        obtain ⟨Y', hY'inj, hY'r, hY'⟩ := ih Y₁ (by omega) hY₁r
        refine ⟨Y', hY'inj, hY'r, ?_⟩
        have e1 : moveCost Y Y₁ = dist (Y j) (Z j) := mc_to_update Y j (Z j)
        have e2 : moveCost Y₁ Z = moveCost Y Z - dist (Y j) (Z j) := by
          rw [hY₁, mc_update_left Y Z j (Z j)]
          simp
        have e3 := mc_triangle Y Y₁ Y'
        linarith
