-- Prove2me | solution 1 for KServer.gamPot_corner_dispatch
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T18:48:23.720818+00:00
-- url     : https://prove2.me/submissions/06c04ae6-4343-4024-b79b-ca8264f47adc

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_quasiconvex_three
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_lazyPot_ge_instance
import Theorems.Thm_KServer_gamPot_instance_le_lazyPot_cases

open KServer

section Perm
variable {M : Type} [MetricSpace M]

private theorem perm3_eq (C₀ : Config 3 M) (σ : List M) (X Y : Config 3 M)
    (τ : Equiv.Perm (Fin 3)) (h : ∀ i, X i = Y (τ i)) :
    workFnU C₀ σ X = workFnU C₀ σ Y := by
  rw [show X = Y ∘ (τ : Equiv.Perm (Fin 3)) from funext h]
  exact workFnU_perm 3 M C₀ σ Y τ

private theorem swap01 (C₀ : Config 3 M) (σ : List M) (p q z : M) :
    workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![q, p, z] := by
  refine perm3_eq C₀ σ _ _ (Equiv.swap 0 1) ?_
  intro i
  match i with
  | 0 => show p = ![q, p, z] ((Equiv.swap (0 : Fin 3) 1) 0); rw [Equiv.swap_apply_left]; rfl
  | 1 => show q = ![q, p, z] ((Equiv.swap (0 : Fin 3) 1) 1); rw [Equiv.swap_apply_right]; rfl
  | 2 => show z = ![q, p, z] ((Equiv.swap (0 : Fin 3) 1) 2)
         rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; rfl

private theorem rot3 (C₀ : Config 3 M) (σ : List M) (p q z : M) :
    workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![z, p, q] := by
  set c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2 with hc
  have c0 : c 0 = 1 := by rw [hc]; decide
  have c1 : c 1 = 2 := by rw [hc]; decide
  have c2 : c 2 = 0 := by rw [hc]; decide
  refine perm3_eq C₀ σ _ _ c ?_
  intro i
  match i with
  | 0 => show p = ![z, p, q] (c 0); rw [c0]; rfl
  | 1 => show q = ![z, p, q] (c 1); rw [c1]; rfl
  | 2 => show z = ![z, p, q] (c 2); rw [c2]; rfl

private theorem swap12 (C₀ : Config 3 M) (σ : List M) (p q z : M) :
    workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![p, z, q] :=
  ((rot3 C₀ σ p z q).trans (swap01 C₀ σ q p z)).symm

/-- The Lipschitz property in pinned two-point form. -/
private theorem lipP (C₀ : Config 3 M) (σ : List M) (r u v v' : M) :
    workFnU C₀ σ ![r, u, v'] ≤ workFnU C₀ σ ![r, v, v'] + dist v u := by
  have hmc : moveCost (![r, v, v'] : Config 3 M) (![r, u, v'] : Config 3 M) = dist v u := by
    unfold moveCost
    rw [Fin.sum_univ_three]
    show dist r r + dist v u + dist v' v' = dist v u
    rw [dist_self, dist_self]; ring
  have h := workFnU_lipschitz 3 (by norm_num) M C₀ σ ![r, u, v'] ![r, v, v']
  rw [hmc] at h
  exact h

end Perm

section GamAlg
variable {M : Type} [MetricSpace M] (C₀ : Config 3 M) (σ : List M) (r : M)

/-- One instance of the auxiliary potential `Γ`. -/
private noncomputable def GamI (p b b' q d d' f : M) : ℝ :=
  (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
    + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
    + dist q f - workFnU C₀ σ ![r, p, f]

private theorem GamI_swapB (p b b' q d d' f : M) :
    GamI C₀ σ r p b b' q d d' f = GamI C₀ σ r p b' b q d d' f := by
  unfold GamI; rw [swap12 C₀ σ r b b']; ring

private theorem GamI_swapD (p b b' q d d' f : M) :
    GamI C₀ σ r p b b' q d d' f = GamI C₀ σ r p b b' q d' d f := by
  unfold GamI; rw [dist_comm d d']; ring

private theorem g1 (p q b b' d' f : M) :
    GamI C₀ σ r p b b' q f d' f ≤ lazyPot C₀ σ r :=
  (gamPot_instance_le_lazyPot_cases M C₀ σ r).1 p q b b' d' f

private theorem g2 (p q b b' d d' f : M) (h1 : dist p b + dist p b' = dist b b')
    (h2 : dist r b + dist r b' = dist b b') :
    GamI C₀ σ r p b b' q d d' f ≤ lazyPot C₀ σ r :=
  (gamPot_instance_le_lazyPot_cases M C₀ σ r).2.1 p q b b' d d' f h1 h2

private theorem g3red (p X q b d d' f : M) (h : dist X p + dist p b = dist X b) :
    GamI C₀ σ r p b b q d d' f ≤ GamI C₀ σ r X b b q d d' f :=
  (gamPot_instance_le_lazyPot_cases M C₀ σ r).2.2.1 p X q b d d' f h

private theorem g31 (p q b d d' : M) :
    GamI C₀ σ r p b b q d d' p ≤ lazyPot C₀ σ r :=
  (gamPot_instance_le_lazyPot_cases M C₀ σ r).2.2.2.1 p q b d d'

private theorem g32 (p q b d d' : M) (h : dist q p + dist q b = dist p b) :
    GamI C₀ σ r p b b q d d' b ≤ lazyPot C₀ σ r :=
  (gamPot_instance_le_lazyPot_cases M C₀ σ r).2.2.2.2.1 p q b d d' h

private theorem g331 (p q b f : M) :
    GamI C₀ σ r p b b q p b f ≤ lazyPot C₀ σ r :=
  (gamPot_instance_le_lazyPot_cases M C₀ σ r).2.2.2.2.2.1 p q b f

private theorem g41 (p q b b' d f : M) (h : dist q b' + dist q f = dist b' f) :
    GamI C₀ σ r p b b' q d b f ≤ lazyPot C₀ σ r :=
  (gamPot_instance_le_lazyPot_cases M C₀ σ r).2.2.2.2.2.2.1 p q b b' d f h

private theorem g42 (p q b b' d : M) :
    GamI C₀ σ r p b b' q d b b' ≤ lazyPot C₀ σ r :=
  (gamPot_instance_le_lazyPot_cases M C₀ σ r).2.2.2.2.2.2.2 p q b b' d

end GamAlg

set_option maxHeartbeats 2000000 in
/-- **The corner case analysis of Lemma 6.** -/
theorem solution (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r x z y t p q : M)
    (hp1 : dist x p + dist p y = dist x y) (hp2 : dist z p + dist p t = dist z t)
    (hq1 : dist x q + dist q y = dist x y) (hq2 : dist z q + dist q t = dist z t)
    (hr1 : dist x r + dist r y = dist x y) (hr2 : dist z r + dist r t = dist z t)
    (B B' F D D' : M)
    (hB : B = x ∨ B = z ∨ B = y ∨ B = t)
    (hB' : B' = x ∨ B' = z ∨ B' = y ∨ B' = t)
    (hF : F = x ∨ F = z ∨ F = y ∨ F = t)
    (hDD : (D = x ∧ D' = y) ∨ (D = z ∧ D' = t) ∨ (D = y ∧ D' = x) ∨ (D = t ∧ D' = z)) :
    (-dist r p + (dist p B + dist p B' - workFnU C₀ σ ![r, B, B']))
      + dist r q + dist D D' - workFnU C₀ σ ![r, q, D] - workFnU C₀ σ ![r, q, D']
      + dist q F - workFnU C₀ σ ![r, p, F]
      ≤ lazyPot C₀ σ r := by
  have mp_xy : dist p x + dist p y = dist x y := by linarith [dist_comm p x, dist_comm p y, dist_comm x y]
  have mp_zt : dist p z + dist p t = dist z t := by linarith [dist_comm p z, dist_comm p t, dist_comm z t]
  have mp_yx : dist p y + dist p x = dist y x := by linarith [dist_comm p y, dist_comm p x, dist_comm y x]
  have mp_tz : dist p t + dist p z = dist t z := by linarith [dist_comm p t, dist_comm p z, dist_comm t z]
  have mq_xy : dist q x + dist q y = dist x y := by linarith [dist_comm q x, dist_comm q y, dist_comm x y]
  have mq_zt : dist q z + dist q t = dist z t := by linarith [dist_comm q z, dist_comm q t, dist_comm z t]
  have mq_yx : dist q y + dist q x = dist y x := by linarith [dist_comm q y, dist_comm q x, dist_comm y x]
  have mq_tz : dist q t + dist q z = dist t z := by linarith [dist_comm q t, dist_comm q z, dist_comm t z]
  have mr_xy : dist r x + dist r y = dist x y := by linarith [dist_comm r x, dist_comm r y, dist_comm x y]
  have mr_zt : dist r z + dist r t = dist z t := by linarith [dist_comm r z, dist_comm r t, dist_comm z t]
  have mr_yx : dist r y + dist r x = dist y x := by linarith [dist_comm r y, dist_comm r x, dist_comm y x]
  have mr_tz : dist r t + dist r z = dist t z := by linarith [dist_comm r t, dist_comm r z, dist_comm t z]
  have lp_xy : dist x p + dist p y = dist x y := by linarith [dist_comm p x, dist_comm p y, dist_comm x y]
  have lp_zt : dist z p + dist p t = dist z t := by linarith [dist_comm p z, dist_comm p t, dist_comm z t]
  have lp_yx : dist y p + dist p x = dist y x := by linarith [dist_comm p y, dist_comm p x, dist_comm y x]
  have lp_tz : dist t p + dist p z = dist t z := by linarith [dist_comm p t, dist_comm p z, dist_comm t z]
  show GamI C₀ σ r p B B' q D D' F ≤ lazyPot C₀ σ r
  rcases hB with e1 | e1 | e1 | e1 <;>
    rcases hB' with e2 | e2 | e2 | e2 <;>
      rcases hF with e3 | e3 | e3 | e3 <;>
        rcases hDD with ⟨e4, e5⟩ | ⟨e4, e5⟩ | ⟨e4, e5⟩ | ⟨e4, e5⟩ <;>
          rw [e1, e2, e3, e4, e5]
  · exact g1 C₀ σ r p q x x y x
  · refine le_trans (g3red C₀ σ r p y q x z t x lp_yx) ?_; exact g32 C₀ σ r y q x z t mq_yx
  · refine le_trans (g3red C₀ σ r p y q x y x x lp_yx) ?_; exact g32 C₀ σ r y q x y x mq_yx
  · refine le_trans (g3red C₀ σ r p y q x t z x lp_yx) ?_; exact g32 C₀ σ r y q x t z mq_yx
  · rw [GamI_swapD]; refine le_trans (g3red C₀ σ r p y q x y x z lp_yx) ?_; exact g331 C₀ σ r y q x z
  · exact g1 C₀ σ r p q x x t z
  · refine le_trans (g3red C₀ σ r p y q x y x z lp_yx) ?_; exact g331 C₀ σ r y q x z
  · rw [GamI_swapD]; exact g1 C₀ σ r p q x x t z
  · refine le_trans (g3red C₀ σ r p y q x x y y lp_yx) ?_; exact g31 C₀ σ r y q x x y
  · refine le_trans (g3red C₀ σ r p y q x z t y lp_yx) ?_; exact g31 C₀ σ r y q x z t
  · exact g1 C₀ σ r p q x x x y
  · refine le_trans (g3red C₀ σ r p y q x t z y lp_yx) ?_; exact g31 C₀ σ r y q x t z
  · rw [GamI_swapD]; refine le_trans (g3red C₀ σ r p y q x y x t lp_yx) ?_; exact g331 C₀ σ r y q x t
  · rw [GamI_swapD]; exact g1 C₀ σ r p q x x z t
  · refine le_trans (g3red C₀ σ r p y q x y x t lp_yx) ?_; exact g331 C₀ σ r y q x t
  · exact g1 C₀ σ r p q x x z t
  · exact g1 C₀ σ r p q x z y x
  · rw [GamI_swapB, GamI_swapD]; exact g42 C₀ σ r p q z x t
  · rw [GamI_swapD]; exact g1 C₀ σ r p q x z y x
  · rw [GamI_swapB]; exact g42 C₀ σ r p q z x t
  · rw [GamI_swapD]; exact g42 C₀ σ r p q x z y
  · exact g1 C₀ σ r p q x z t z
  · exact g42 C₀ σ r p q x z y
  · rw [GamI_swapD]; exact g1 C₀ σ r p q x z t z
  · rw [GamI_swapD]; exact g1 C₀ σ r p q x z x y
  · rw [GamI_swapB, GamI_swapD]; exact g41 C₀ σ r p q z x t y mq_xy
  · exact g1 C₀ σ r p q x z x y
  · rw [GamI_swapB]; exact g41 C₀ σ r p q z x t y mq_xy
  · rw [GamI_swapD]; exact g41 C₀ σ r p q x z y t mq_zt
  · rw [GamI_swapD]; exact g1 C₀ σ r p q x z z t
  · exact g41 C₀ σ r p q x z y t mq_zt
  · exact g1 C₀ σ r p q x z z t
  · exact g1 C₀ σ r p q x y y x
  · exact g2 C₀ σ r p q x y z t x mp_xy mr_xy
  · exact g2 C₀ σ r p q x y y x x mp_xy mr_xy
  · exact g2 C₀ σ r p q x y t z x mp_xy mr_xy
  · exact g2 C₀ σ r p q x y x y z mp_xy mr_xy
  · exact g1 C₀ σ r p q x y t z
  · exact g2 C₀ σ r p q x y y x z mp_xy mr_xy
  · exact g2 C₀ σ r p q x y t z z mp_xy mr_xy
  · exact g2 C₀ σ r p q x y x y y mp_xy mr_xy
  · exact g2 C₀ σ r p q x y z t y mp_xy mr_xy
  · exact g1 C₀ σ r p q x y x y
  · exact g2 C₀ σ r p q x y t z y mp_xy mr_xy
  · exact g2 C₀ σ r p q x y x y t mp_xy mr_xy
  · exact g2 C₀ σ r p q x y z t t mp_xy mr_xy
  · exact g2 C₀ σ r p q x y y x t mp_xy mr_xy
  · exact g1 C₀ σ r p q x y z t
  · exact g1 C₀ σ r p q x t y x
  · rw [GamI_swapB]; exact g42 C₀ σ r p q t x z
  · rw [GamI_swapD]; exact g1 C₀ σ r p q x t y x
  · rw [GamI_swapB, GamI_swapD]; exact g42 C₀ σ r p q t x z
  · rw [GamI_swapD]; exact g41 C₀ σ r p q x t y z mq_tz
  · exact g1 C₀ σ r p q x t t z
  · exact g41 C₀ σ r p q x t y z mq_tz
  · rw [GamI_swapD]; exact g1 C₀ σ r p q x t t z
  · rw [GamI_swapD]; exact g1 C₀ σ r p q x t x y
  · rw [GamI_swapB]; exact g41 C₀ σ r p q t x z y mq_xy
  · exact g1 C₀ σ r p q x t x y
  · rw [GamI_swapB, GamI_swapD]; exact g41 C₀ σ r p q t x z y mq_xy
  · rw [GamI_swapD]; exact g42 C₀ σ r p q x t y
  · rw [GamI_swapD]; exact g1 C₀ σ r p q x t z t
  · exact g42 C₀ σ r p q x t y
  · exact g1 C₀ σ r p q x t z t
  · exact g1 C₀ σ r p q z x y x
  · rw [GamI_swapD]; exact g42 C₀ σ r p q z x t
  · rw [GamI_swapD]; exact g1 C₀ σ r p q z x y x
  · exact g42 C₀ σ r p q z x t
  · rw [GamI_swapB, GamI_swapD]; exact g42 C₀ σ r p q x z y
  · exact g1 C₀ σ r p q z x t z
  · rw [GamI_swapB]; exact g42 C₀ σ r p q x z y
  · rw [GamI_swapD]; exact g1 C₀ σ r p q z x t z
  · rw [GamI_swapD]; exact g1 C₀ σ r p q z x x y
  · rw [GamI_swapD]; exact g41 C₀ σ r p q z x t y mq_xy
  · exact g1 C₀ σ r p q z x x y
  · exact g41 C₀ σ r p q z x t y mq_xy
  · rw [GamI_swapB, GamI_swapD]; exact g41 C₀ σ r p q x z y t mq_zt
  · rw [GamI_swapD]; exact g1 C₀ σ r p q z x z t
  · rw [GamI_swapB]; exact g41 C₀ σ r p q x z y t mq_zt
  · exact g1 C₀ σ r p q z x z t
  · exact g1 C₀ σ r p q z z y x
  · rw [GamI_swapD]; refine le_trans (g3red C₀ σ r p t q z t z x lp_tz) ?_; exact g331 C₀ σ r t q z x
  · rw [GamI_swapD]; exact g1 C₀ σ r p q z z y x
  · refine le_trans (g3red C₀ σ r p t q z t z x lp_tz) ?_; exact g331 C₀ σ r t q z x
  · refine le_trans (g3red C₀ σ r p t q z x y z lp_tz) ?_; exact g32 C₀ σ r t q z x y mq_tz
  · exact g1 C₀ σ r p q z z t z
  · refine le_trans (g3red C₀ σ r p t q z y x z lp_tz) ?_; exact g32 C₀ σ r t q z y x mq_tz
  · refine le_trans (g3red C₀ σ r p t q z t z z lp_tz) ?_; exact g32 C₀ σ r t q z t z mq_tz
  · rw [GamI_swapD]; exact g1 C₀ σ r p q z z x y
  · rw [GamI_swapD]; refine le_trans (g3red C₀ σ r p t q z t z y lp_tz) ?_; exact g331 C₀ σ r t q z y
  · exact g1 C₀ σ r p q z z x y
  · refine le_trans (g3red C₀ σ r p t q z t z y lp_tz) ?_; exact g331 C₀ σ r t q z y
  · refine le_trans (g3red C₀ σ r p t q z x y t lp_tz) ?_; exact g31 C₀ σ r t q z x y
  · refine le_trans (g3red C₀ σ r p t q z z t t lp_tz) ?_; exact g31 C₀ σ r t q z z t
  · refine le_trans (g3red C₀ σ r p t q z y x t lp_tz) ?_; exact g31 C₀ σ r t q z y x
  · exact g1 C₀ σ r p q z z z t
  · exact g1 C₀ σ r p q z y y x
  · rw [GamI_swapD]; exact g41 C₀ σ r p q z y t x mq_yx
  · rw [GamI_swapD]; exact g1 C₀ σ r p q z y y x
  · exact g41 C₀ σ r p q z y t x mq_yx
  · rw [GamI_swapB]; exact g42 C₀ σ r p q y z x
  · exact g1 C₀ σ r p q z y t z
  · rw [GamI_swapB, GamI_swapD]; exact g42 C₀ σ r p q y z x
  · rw [GamI_swapD]; exact g1 C₀ σ r p q z y t z
  · rw [GamI_swapD]; exact g1 C₀ σ r p q z y x y
  · rw [GamI_swapD]; exact g42 C₀ σ r p q z y t
  · exact g1 C₀ σ r p q z y x y
  · exact g42 C₀ σ r p q z y t
  · rw [GamI_swapB]; exact g41 C₀ σ r p q y z x t mq_zt
  · rw [GamI_swapD]; exact g1 C₀ σ r p q z y z t
  · rw [GamI_swapB, GamI_swapD]; exact g41 C₀ σ r p q y z x t mq_zt
  · exact g1 C₀ σ r p q z y z t
  · exact g1 C₀ σ r p q z t y x
  · exact g2 C₀ σ r p q z t z t x mp_zt mr_zt
  · exact g2 C₀ σ r p q z t y x x mp_zt mr_zt
  · exact g2 C₀ σ r p q z t t z x mp_zt mr_zt
  · exact g2 C₀ σ r p q z t x y z mp_zt mr_zt
  · exact g1 C₀ σ r p q z t t z
  · exact g2 C₀ σ r p q z t y x z mp_zt mr_zt
  · exact g2 C₀ σ r p q z t t z z mp_zt mr_zt
  · exact g2 C₀ σ r p q z t x y y mp_zt mr_zt
  · exact g2 C₀ σ r p q z t z t y mp_zt mr_zt
  · exact g1 C₀ σ r p q z t x y
  · exact g2 C₀ σ r p q z t t z y mp_zt mr_zt
  · exact g2 C₀ σ r p q z t x y t mp_zt mr_zt
  · exact g2 C₀ σ r p q z t z t t mp_zt mr_zt
  · exact g2 C₀ σ r p q z t y x t mp_zt mr_zt
  · exact g1 C₀ σ r p q z t z t
  · exact g1 C₀ σ r p q y x y x
  · exact g2 C₀ σ r p q y x z t x mp_yx mr_yx
  · exact g2 C₀ σ r p q y x y x x mp_yx mr_yx
  · exact g2 C₀ σ r p q y x t z x mp_yx mr_yx
  · exact g2 C₀ σ r p q y x x y z mp_yx mr_yx
  · exact g1 C₀ σ r p q y x t z
  · exact g2 C₀ σ r p q y x y x z mp_yx mr_yx
  · exact g2 C₀ σ r p q y x t z z mp_yx mr_yx
  · exact g2 C₀ σ r p q y x x y y mp_yx mr_yx
  · exact g2 C₀ σ r p q y x z t y mp_yx mr_yx
  · exact g1 C₀ σ r p q y x x y
  · exact g2 C₀ σ r p q y x t z y mp_yx mr_yx
  · exact g2 C₀ σ r p q y x x y t mp_yx mr_yx
  · exact g2 C₀ σ r p q y x z t t mp_yx mr_yx
  · exact g2 C₀ σ r p q y x y x t mp_yx mr_yx
  · exact g1 C₀ σ r p q y x z t
  · exact g1 C₀ σ r p q y z y x
  · rw [GamI_swapB, GamI_swapD]; exact g41 C₀ σ r p q z y t x mq_yx
  · rw [GamI_swapD]; exact g1 C₀ σ r p q y z y x
  · rw [GamI_swapB]; exact g41 C₀ σ r p q z y t x mq_yx
  · exact g42 C₀ σ r p q y z x
  · exact g1 C₀ σ r p q y z t z
  · rw [GamI_swapD]; exact g42 C₀ σ r p q y z x
  · rw [GamI_swapD]; exact g1 C₀ σ r p q y z t z
  · rw [GamI_swapD]; exact g1 C₀ σ r p q y z x y
  · rw [GamI_swapB, GamI_swapD]; exact g42 C₀ σ r p q z y t
  · exact g1 C₀ σ r p q y z x y
  · rw [GamI_swapB]; exact g42 C₀ σ r p q z y t
  · exact g41 C₀ σ r p q y z x t mq_zt
  · rw [GamI_swapD]; exact g1 C₀ σ r p q y z z t
  · rw [GamI_swapD]; exact g41 C₀ σ r p q y z x t mq_zt
  · exact g1 C₀ σ r p q y z z t
  · exact g1 C₀ σ r p q y y y x
  · refine le_trans (g3red C₀ σ r p x q y z t x lp_xy) ?_; exact g31 C₀ σ r x q y z t
  · refine le_trans (g3red C₀ σ r p x q y y x x lp_xy) ?_; exact g31 C₀ σ r x q y y x
  · refine le_trans (g3red C₀ σ r p x q y t z x lp_xy) ?_; exact g31 C₀ σ r x q y t z
  · refine le_trans (g3red C₀ σ r p x q y x y z lp_xy) ?_; exact g331 C₀ σ r x q y z
  · exact g1 C₀ σ r p q y y t z
  · rw [GamI_swapD]; refine le_trans (g3red C₀ σ r p x q y x y z lp_xy) ?_; exact g331 C₀ σ r x q y z
  · rw [GamI_swapD]; exact g1 C₀ σ r p q y y t z
  · refine le_trans (g3red C₀ σ r p x q y x y y lp_xy) ?_; exact g32 C₀ σ r x q y x y mq_xy
  · refine le_trans (g3red C₀ σ r p x q y z t y lp_xy) ?_; exact g32 C₀ σ r x q y z t mq_xy
  · exact g1 C₀ σ r p q y y x y
  · refine le_trans (g3red C₀ σ r p x q y t z y lp_xy) ?_; exact g32 C₀ σ r x q y t z mq_xy
  · refine le_trans (g3red C₀ σ r p x q y x y t lp_xy) ?_; exact g331 C₀ σ r x q y t
  · rw [GamI_swapD]; exact g1 C₀ σ r p q y y z t
  · rw [GamI_swapD]; refine le_trans (g3red C₀ σ r p x q y x y t lp_xy) ?_; exact g331 C₀ σ r x q y t
  · exact g1 C₀ σ r p q y y z t
  · exact g1 C₀ σ r p q y t y x
  · rw [GamI_swapB]; exact g41 C₀ σ r p q t y z x mq_yx
  · rw [GamI_swapD]; exact g1 C₀ σ r p q y t y x
  · rw [GamI_swapB, GamI_swapD]; exact g41 C₀ σ r p q t y z x mq_yx
  · exact g41 C₀ σ r p q y t x z mq_tz
  · exact g1 C₀ σ r p q y t t z
  · rw [GamI_swapD]; exact g41 C₀ σ r p q y t x z mq_tz
  · rw [GamI_swapD]; exact g1 C₀ σ r p q y t t z
  · rw [GamI_swapD]; exact g1 C₀ σ r p q y t x y
  · rw [GamI_swapB]; exact g42 C₀ σ r p q t y z
  · exact g1 C₀ σ r p q y t x y
  · rw [GamI_swapB, GamI_swapD]; exact g42 C₀ σ r p q t y z
  · exact g42 C₀ σ r p q y t x
  · rw [GamI_swapD]; exact g1 C₀ σ r p q y t z t
  · rw [GamI_swapD]; exact g42 C₀ σ r p q y t x
  · exact g1 C₀ σ r p q y t z t
  · exact g1 C₀ σ r p q t x y x
  · exact g42 C₀ σ r p q t x z
  · rw [GamI_swapD]; exact g1 C₀ σ r p q t x y x
  · rw [GamI_swapD]; exact g42 C₀ σ r p q t x z
  · rw [GamI_swapB, GamI_swapD]; exact g41 C₀ σ r p q x t y z mq_tz
  · exact g1 C₀ σ r p q t x t z
  · rw [GamI_swapB]; exact g41 C₀ σ r p q x t y z mq_tz
  · rw [GamI_swapD]; exact g1 C₀ σ r p q t x t z
  · rw [GamI_swapD]; exact g1 C₀ σ r p q t x x y
  · exact g41 C₀ σ r p q t x z y mq_xy
  · exact g1 C₀ σ r p q t x x y
  · rw [GamI_swapD]; exact g41 C₀ σ r p q t x z y mq_xy
  · rw [GamI_swapB, GamI_swapD]; exact g42 C₀ σ r p q x t y
  · rw [GamI_swapD]; exact g1 C₀ σ r p q t x z t
  · rw [GamI_swapB]; exact g42 C₀ σ r p q x t y
  · exact g1 C₀ σ r p q t x z t
  · exact g1 C₀ σ r p q t z y x
  · exact g2 C₀ σ r p q t z z t x mp_tz mr_tz
  · exact g2 C₀ σ r p q t z y x x mp_tz mr_tz
  · exact g2 C₀ σ r p q t z t z x mp_tz mr_tz
  · exact g2 C₀ σ r p q t z x y z mp_tz mr_tz
  · exact g1 C₀ σ r p q t z t z
  · exact g2 C₀ σ r p q t z y x z mp_tz mr_tz
  · exact g2 C₀ σ r p q t z t z z mp_tz mr_tz
  · exact g2 C₀ σ r p q t z x y y mp_tz mr_tz
  · exact g2 C₀ σ r p q t z z t y mp_tz mr_tz
  · exact g1 C₀ σ r p q t z x y
  · exact g2 C₀ σ r p q t z t z y mp_tz mr_tz
  · exact g2 C₀ σ r p q t z x y t mp_tz mr_tz
  · exact g2 C₀ σ r p q t z z t t mp_tz mr_tz
  · exact g2 C₀ σ r p q t z y x t mp_tz mr_tz
  · exact g1 C₀ σ r p q t z z t
  · exact g1 C₀ σ r p q t y y x
  · exact g41 C₀ σ r p q t y z x mq_yx
  · rw [GamI_swapD]; exact g1 C₀ σ r p q t y y x
  · rw [GamI_swapD]; exact g41 C₀ σ r p q t y z x mq_yx
  · rw [GamI_swapB]; exact g41 C₀ σ r p q y t x z mq_tz
  · exact g1 C₀ σ r p q t y t z
  · rw [GamI_swapB, GamI_swapD]; exact g41 C₀ σ r p q y t x z mq_tz
  · rw [GamI_swapD]; exact g1 C₀ σ r p q t y t z
  · rw [GamI_swapD]; exact g1 C₀ σ r p q t y x y
  · exact g42 C₀ σ r p q t y z
  · exact g1 C₀ σ r p q t y x y
  · rw [GamI_swapD]; exact g42 C₀ σ r p q t y z
  · rw [GamI_swapB]; exact g42 C₀ σ r p q y t x
  · rw [GamI_swapD]; exact g1 C₀ σ r p q t y z t
  · rw [GamI_swapB, GamI_swapD]; exact g42 C₀ σ r p q y t x
  · exact g1 C₀ σ r p q t y z t
  · exact g1 C₀ σ r p q t t y x
  · refine le_trans (g3red C₀ σ r p z q t z t x lp_zt) ?_; exact g331 C₀ σ r z q t x
  · rw [GamI_swapD]; exact g1 C₀ σ r p q t t y x
  · rw [GamI_swapD]; refine le_trans (g3red C₀ σ r p z q t z t x lp_zt) ?_; exact g331 C₀ σ r z q t x
  · refine le_trans (g3red C₀ σ r p z q t x y z lp_zt) ?_; exact g31 C₀ σ r z q t x y
  · exact g1 C₀ σ r p q t t t z
  · refine le_trans (g3red C₀ σ r p z q t y x z lp_zt) ?_; exact g31 C₀ σ r z q t y x
  · refine le_trans (g3red C₀ σ r p z q t t z z lp_zt) ?_; exact g31 C₀ σ r z q t t z
  · rw [GamI_swapD]; exact g1 C₀ σ r p q t t x y
  · refine le_trans (g3red C₀ σ r p z q t z t y lp_zt) ?_; exact g331 C₀ σ r z q t y
  · exact g1 C₀ σ r p q t t x y
  · rw [GamI_swapD]; refine le_trans (g3red C₀ σ r p z q t z t y lp_zt) ?_; exact g331 C₀ σ r z q t y
  · refine le_trans (g3red C₀ σ r p z q t x y t lp_zt) ?_; exact g32 C₀ σ r z q t x y mq_zt
  · refine le_trans (g3red C₀ σ r p z q t z t t lp_zt) ?_; exact g32 C₀ σ r z q t z t mq_zt
  · refine le_trans (g3red C₀ σ r p z q t y x t lp_zt) ?_; exact g32 C₀ σ r z q t y x mq_zt
  · exact g1 C₀ σ r p q t t z t
