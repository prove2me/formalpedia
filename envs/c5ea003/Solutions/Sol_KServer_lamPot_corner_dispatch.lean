-- Prove2me | solution 1 for KServer.lamPot_corner_dispatch
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T18:30:14.271467+00:00
-- url     : https://prove2.me/submissions/ef9c3d52-acae-446e-9fa9-938502943b07

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_lamPot_instance_le_lazyPot_special
import Theorems.Thm_KServer_lamPot_instance_le_lazyPot_adjacent

open KServer

section Perm5
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

end Perm5

section LamAlg
variable {M : Type} [MetricSpace M] (C₀ : Config 3 M) (σ : List M) (r : M)

/-- One instance of the auxiliary potential `Λ`. -/
private noncomputable def LamI (p b b' q c c' e e' : M) : ℝ :=
  (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
    + (-dist r q + (dist q c + dist q c' - workFnU C₀ σ ![r, c, c']))
    - workFnU C₀ σ ![r, p, q] + dist e e' - workFnU C₀ σ ![r, e, e']

private theorem LamI_swapB (p b b' q c c' e e' : M) :
    LamI C₀ σ r p b b' q c c' e e' = LamI C₀ σ r p b' b q c c' e e' := by
  unfold LamI; rw [swap12 C₀ σ r b b']; ring

private theorem LamI_swapC (p b b' q c c' e e' : M) :
    LamI C₀ σ r p b b' q c c' e e' = LamI C₀ σ r p b b' q c' c e e' := by
  unfold LamI; rw [swap12 C₀ σ r c c']; ring

private theorem LamI_swapE (p b b' q c c' e e' : M) :
    LamI C₀ σ r p b b' q c c' e e' = LamI C₀ σ r p b b' q c c' e' e := by
  unfold LamI; rw [swap12 C₀ σ r e e', dist_comm e e']

private theorem LamI_exch (p b b' q c c' e e' : M) :
    LamI C₀ σ r p b b' q c c' e e' = LamI C₀ σ r q c c' p b b' e e' := by
  unfold LamI; rw [swap12 C₀ σ r p q]; ring

/-- Case 1. -/
private theorem cse1 (p q b b' c c' e e' : M) (h : dist p b + dist p b' = dist b b') :
    LamI C₀ σ r p b b' q c c' e e' ≤ lazyPot C₀ σ r :=
  (lamPot_instance_le_lazyPot_special M C₀ σ r).1 p q b b' c c' e e' h

/-- Case 2.1. -/
private theorem cse21 (p q b c' e e' : M) :
    LamI C₀ σ r p b b q b c' e e' ≤ lazyPot C₀ σ r :=
  (lamPot_instance_le_lazyPot_special M C₀ σ r).2.1 p q b c' e e'

/-- Case 2.2. -/
private theorem cse22 (p q b c c' e e' : M) (h : dist p c + dist p b = dist c b) :
    LamI C₀ σ r p b b q c c' e e' ≤ lazyPot C₀ σ r :=
  (lamPot_instance_le_lazyPot_special M C₀ σ r).2.2 p q b c c' e e' h

/-- Case 2.3. -/
private theorem cse23 (p q B C E : M) (h : dist E p + dist p B = dist E B) :
    LamI C₀ σ r p B B q C C E B ≤ lazyPot C₀ σ r :=
  (lamPot_instance_le_lazyPot_adjacent M C₀ σ r).1 p q B C E h

/-- Case 3.1. -/
private theorem cse31 (p q B B' C C' e e' : M)
    (h1 : dist q C + dist q B = dist C B) (h2 : dist q B' + dist q C' = dist B' C') :
    LamI C₀ σ r p B B' q C C' e e' ≤ lazyPot C₀ σ r :=
  (lamPot_instance_le_lazyPot_adjacent M C₀ σ r).2.1 p q B B' C C' e e' h1 h2

/-- Case 3.2. -/
private theorem cse32 (p q B B' C' e e' : M) (h : dist q B' + dist q C' = dist B' C') :
    LamI C₀ σ r p B B' q B C' e e' ≤ lazyPot C₀ σ r :=
  (lamPot_instance_le_lazyPot_adjacent M C₀ σ r).2.2.1 p q B B' C' e e' h

/-- Case 3.3. -/
private theorem cse33 (p q B B' E : M) :
    LamI C₀ σ r p B B' q B B' E B ≤ lazyPot C₀ σ r :=
  (lamPot_instance_le_lazyPot_adjacent M C₀ σ r).2.2.2 p q B B' E

end LamAlg


set_option maxHeartbeats 4000000 in
/-- **The corner case analysis of Lemma 5.** -/
theorem solution (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r x z y t p q : M)
    (hp1 : dist x p + dist p y = dist x y) (hp2 : dist z p + dist p t = dist z t)
    (hq1 : dist x q + dist q y = dist x y) (hq2 : dist z q + dist q t = dist z t)
    (B B' C C' E E' : M)
    (hB : B = x ∨ B = z ∨ B = y ∨ B = t)
    (hB' : B' = x ∨ B' = z ∨ B' = y ∨ B' = t)
    (hC : C = x ∨ C = z ∨ C = y ∨ C = t)
    (hC' : C' = x ∨ C' = z ∨ C' = y ∨ C' = t)
    (hEE : (E = x ∧ E' = y) ∨ (E = z ∧ E' = t) ∨ (E = y ∧ E' = x) ∨ (E = t ∧ E' = z)) :
    (-dist r p + (dist p B + dist p B' - workFnU C₀ σ ![r, B, B']))
      + (-dist r q + (dist q C + dist q C' - workFnU C₀ σ ![r, C, C']))
      - workFnU C₀ σ ![r, p, q] + dist E E' - workFnU C₀ σ ![r, E, E']
      ≤ lazyPot C₀ σ r := by
  have mp_xy : dist p x + dist p y = dist x y := by linarith [dist_comm p x, dist_comm p y, dist_comm x y]
  have lp_xy : dist x p + dist p y = dist x y := by linarith [dist_comm p x, dist_comm p y, dist_comm x y]
  have mp_yx : dist p y + dist p x = dist y x := by linarith [dist_comm p y, dist_comm p x, dist_comm y x]
  have lp_yx : dist y p + dist p x = dist y x := by linarith [dist_comm p y, dist_comm p x, dist_comm y x]
  have mp_zt : dist p z + dist p t = dist z t := by linarith [dist_comm p z, dist_comm p t, dist_comm z t]
  have lp_zt : dist z p + dist p t = dist z t := by linarith [dist_comm p z, dist_comm p t, dist_comm z t]
  have mp_tz : dist p t + dist p z = dist t z := by linarith [dist_comm p t, dist_comm p z, dist_comm t z]
  have lp_tz : dist t p + dist p z = dist t z := by linarith [dist_comm p t, dist_comm p z, dist_comm t z]
  have mq_xy : dist q x + dist q y = dist x y := by linarith [dist_comm q x, dist_comm q y, dist_comm x y]
  have lq_xy : dist x q + dist q y = dist x y := by linarith [dist_comm q x, dist_comm q y, dist_comm x y]
  have mq_yx : dist q y + dist q x = dist y x := by linarith [dist_comm q y, dist_comm q x, dist_comm y x]
  have lq_yx : dist y q + dist q x = dist y x := by linarith [dist_comm q y, dist_comm q x, dist_comm y x]
  have mq_zt : dist q z + dist q t = dist z t := by linarith [dist_comm q z, dist_comm q t, dist_comm z t]
  have lq_zt : dist z q + dist q t = dist z t := by linarith [dist_comm q z, dist_comm q t, dist_comm z t]
  have mq_tz : dist q t + dist q z = dist t z := by linarith [dist_comm q t, dist_comm q z, dist_comm t z]
  have lq_tz : dist t q + dist q z = dist t z := by linarith [dist_comm q t, dist_comm q z, dist_comm t z]
  show LamI C₀ σ r p B B' q C C' E E' ≤ lazyPot C₀ σ r
  rcases hB with e1 | e1 | e1 | e1 <;>
    rcases hB' with e2 | e2 | e2 | e2 <;>
      rcases hC with e3 | e3 | e3 | e3 <;>
        rcases hC' with e4 | e4 | e4 | e4 <;>
          rcases hEE with ⟨e5, e6⟩ | ⟨e5, e6⟩ | ⟨e5, e6⟩ | ⟨e5, e6⟩ <;>
            rw [e1, e2, e3, e4, e5, e6]
  · exact cse21 C₀ σ r p q x x x y
  · exact cse21 C₀ σ r p q x x z t
  · exact cse21 C₀ σ r p q x x y x
  · exact cse21 C₀ σ r p q x x t z
  · exact cse21 C₀ σ r p q x z x y
  · exact cse21 C₀ σ r p q x z z t
  · exact cse21 C₀ σ r p q x z y x
  · exact cse21 C₀ σ r p q x z t z
  · exact cse21 C₀ σ r p q x y x y
  · exact cse21 C₀ σ r p q x y z t
  · exact cse21 C₀ σ r p q x y y x
  · exact cse21 C₀ σ r p q x y t z
  · exact cse21 C₀ σ r p q x t x y
  · exact cse21 C₀ σ r p q x t z t
  · exact cse21 C₀ σ r p q x t y x
  · exact cse21 C₀ σ r p q x t t z
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q x z x y
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q x z z t
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q x z y x
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q x z t z
  · rw [LamI_swapE]; exact cse23 C₀ σ r p q x z y lp_yx
  · rw [LamI_swapE, LamI_exch]; exact cse23 C₀ σ r q p z x t lq_tz
  · exact cse23 C₀ σ r p q x z y lp_yx
  · rw [LamI_exch]; exact cse23 C₀ σ r q p z x t lq_tz
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q x y z x y mp_yx
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q x y z z t mp_yx
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q x y z y x mp_yx
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q x y z t z mp_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t x x x y mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t x x z t mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t x x y x mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t x x t z mq_zt
  · exact cse22 C₀ σ r p q x y x x y mp_yx
  · exact cse22 C₀ σ r p q x y x z t mp_yx
  · exact cse22 C₀ σ r p q x y x y x mp_yx
  · exact cse22 C₀ σ r p q x y x t z mp_yx
  · exact cse22 C₀ σ r p q x y z x y mp_yx
  · exact cse22 C₀ σ r p q x y z z t mp_yx
  · exact cse22 C₀ σ r p q x y z y x mp_yx
  · exact cse22 C₀ σ r p q x y z t z mp_yx
  · exact cse22 C₀ σ r p q x y y x y mp_yx
  · exact cse22 C₀ σ r p q x y y z t mp_yx
  · exact cse22 C₀ σ r p q x y y y x mp_yx
  · exact cse22 C₀ σ r p q x y y t z mp_yx
  · exact cse22 C₀ σ r p q x y t x y mp_yx
  · exact cse22 C₀ σ r p q x y t z t mp_yx
  · exact cse22 C₀ σ r p q x y t y x mp_yx
  · exact cse22 C₀ σ r p q x y t t z mp_yx
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q x t x y
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q x t z t
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q x t y x
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q x t t z
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z x x x y mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z x x z t mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z x x y x mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z x x t z mq_tz
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q x y t x y mp_yx
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q x y t z t mp_yx
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q x y t y x mp_yx
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q x y t t z mp_yx
  · rw [LamI_swapE]; exact cse23 C₀ σ r p q x t y lp_yx
  · rw [LamI_exch]; exact cse23 C₀ σ r q p t x z lq_zt
  · exact cse23 C₀ σ r p q x t y lp_yx
  · rw [LamI_swapE, LamI_exch]; exact cse23 C₀ σ r q p t x z lq_zt
  · rw [LamI_exch]; exact cse21 C₀ σ r q p x z x y
  · rw [LamI_exch]; exact cse21 C₀ σ r q p x z z t
  · rw [LamI_exch]; exact cse21 C₀ σ r q p x z y x
  · rw [LamI_exch]; exact cse21 C₀ σ r q p x z t z
  · rw [LamI_swapE]; exact cse33 C₀ σ r p q x z y
  · rw [LamI_swapB, LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q z x t
  · exact cse33 C₀ σ r p q x z y
  · rw [LamI_swapB, LamI_swapC]; exact cse33 C₀ σ r p q z x t
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y x z x y mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y x z z t mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y x z y x mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y x z t z mq_xy
  · exact cse32 C₀ σ r p q x z t x y mq_zt
  · exact cse32 C₀ σ r p q x z t z t mq_zt
  · exact cse32 C₀ σ r p q x z t y x mq_zt
  · exact cse32 C₀ σ r p q x z t t z mq_zt
  · rw [LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q x z y
  · rw [LamI_swapB, LamI_swapE]; exact cse33 C₀ σ r p q z x t
  · rw [LamI_swapC]; exact cse33 C₀ σ r p q x z y
  · rw [LamI_swapB]; exact cse33 C₀ σ r p q z x t
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p z x x y
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p z x z t
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p z x y x
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p z x t z
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q z x y x y mq_xy
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q z x y z t mq_xy
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q z x y y x mq_xy
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q z x y t z mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t x z x y mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t x z z t mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t x z y x mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t x z t z mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x x z x y mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x x z z t mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x x z y x mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x x z t z mq_yx
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q z x y x y mq_xy
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q z x y z t mq_xy
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q z x y y x mq_xy
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q z x y t z mq_xy
  · rw [LamI_exch]; exact cse22 C₀ σ r q p y x z x y mq_xy
  · rw [LamI_exch]; exact cse22 C₀ σ r q p y x z z t mq_xy
  · rw [LamI_exch]; exact cse22 C₀ σ r q p y x z y x mq_xy
  · rw [LamI_exch]; exact cse22 C₀ σ r q p y x z t z mq_xy
  · exact cse31 C₀ σ r p q x z y t x y mq_yx mq_zt
  · exact cse31 C₀ σ r p q x z y t z t mq_yx mq_zt
  · exact cse31 C₀ σ r p q x z y t y x mq_yx mq_zt
  · exact cse31 C₀ σ r p q x z y t t z mq_yx mq_zt
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q x z t x y mq_zt
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q x z t z t mq_zt
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q x z t y x mq_zt
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q x z t t z mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z x z x y mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z x z z t mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z x z y x mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z x z t z mq_tz
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q z x t y x y mq_tz mq_xy
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q z x t y z t mq_tz mq_xy
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q z x t y y x mq_tz mq_xy
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q z x t y t z mq_tz mq_xy
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p t z x x y mq_zt
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p t z x z t mq_zt
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p t z x y x mq_zt
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p t z x t z mq_zt
  · exact cse1 C₀ σ r p q x y x x x y mp_xy
  · exact cse1 C₀ σ r p q x y x x z t mp_xy
  · exact cse1 C₀ σ r p q x y x x y x mp_xy
  · exact cse1 C₀ σ r p q x y x x t z mp_xy
  · exact cse1 C₀ σ r p q x y x z x y mp_xy
  · exact cse1 C₀ σ r p q x y x z z t mp_xy
  · exact cse1 C₀ σ r p q x y x z y x mp_xy
  · exact cse1 C₀ σ r p q x y x z t z mp_xy
  · exact cse1 C₀ σ r p q x y x y x y mp_xy
  · exact cse1 C₀ σ r p q x y x y z t mp_xy
  · exact cse1 C₀ σ r p q x y x y y x mp_xy
  · exact cse1 C₀ σ r p q x y x y t z mp_xy
  · exact cse1 C₀ σ r p q x y x t x y mp_xy
  · exact cse1 C₀ σ r p q x y x t z t mp_xy
  · exact cse1 C₀ σ r p q x y x t y x mp_xy
  · exact cse1 C₀ σ r p q x y x t t z mp_xy
  · exact cse1 C₀ σ r p q x y z x x y mp_xy
  · exact cse1 C₀ σ r p q x y z x z t mp_xy
  · exact cse1 C₀ σ r p q x y z x y x mp_xy
  · exact cse1 C₀ σ r p q x y z x t z mp_xy
  · exact cse1 C₀ σ r p q x y z z x y mp_xy
  · exact cse1 C₀ σ r p q x y z z z t mp_xy
  · exact cse1 C₀ σ r p q x y z z y x mp_xy
  · exact cse1 C₀ σ r p q x y z z t z mp_xy
  · exact cse1 C₀ σ r p q x y z y x y mp_xy
  · exact cse1 C₀ σ r p q x y z y z t mp_xy
  · exact cse1 C₀ σ r p q x y z y y x mp_xy
  · exact cse1 C₀ σ r p q x y z y t z mp_xy
  · exact cse1 C₀ σ r p q x y z t x y mp_xy
  · exact cse1 C₀ σ r p q x y z t z t mp_xy
  · exact cse1 C₀ σ r p q x y z t y x mp_xy
  · exact cse1 C₀ σ r p q x y z t t z mp_xy
  · exact cse1 C₀ σ r p q x y y x x y mp_xy
  · exact cse1 C₀ σ r p q x y y x z t mp_xy
  · exact cse1 C₀ σ r p q x y y x y x mp_xy
  · exact cse1 C₀ σ r p q x y y x t z mp_xy
  · exact cse1 C₀ σ r p q x y y z x y mp_xy
  · exact cse1 C₀ σ r p q x y y z z t mp_xy
  · exact cse1 C₀ σ r p q x y y z y x mp_xy
  · exact cse1 C₀ σ r p q x y y z t z mp_xy
  · exact cse1 C₀ σ r p q x y y y x y mp_xy
  · exact cse1 C₀ σ r p q x y y y z t mp_xy
  · exact cse1 C₀ σ r p q x y y y y x mp_xy
  · exact cse1 C₀ σ r p q x y y y t z mp_xy
  · exact cse1 C₀ σ r p q x y y t x y mp_xy
  · exact cse1 C₀ σ r p q x y y t z t mp_xy
  · exact cse1 C₀ σ r p q x y y t y x mp_xy
  · exact cse1 C₀ σ r p q x y y t t z mp_xy
  · exact cse1 C₀ σ r p q x y t x x y mp_xy
  · exact cse1 C₀ σ r p q x y t x z t mp_xy
  · exact cse1 C₀ σ r p q x y t x y x mp_xy
  · exact cse1 C₀ σ r p q x y t x t z mp_xy
  · exact cse1 C₀ σ r p q x y t z x y mp_xy
  · exact cse1 C₀ σ r p q x y t z z t mp_xy
  · exact cse1 C₀ σ r p q x y t z y x mp_xy
  · exact cse1 C₀ σ r p q x y t z t z mp_xy
  · exact cse1 C₀ σ r p q x y t y x y mp_xy
  · exact cse1 C₀ σ r p q x y t y z t mp_xy
  · exact cse1 C₀ σ r p q x y t y y x mp_xy
  · exact cse1 C₀ σ r p q x y t y t z mp_xy
  · exact cse1 C₀ σ r p q x y t t x y mp_xy
  · exact cse1 C₀ σ r p q x y t t z t mp_xy
  · exact cse1 C₀ σ r p q x y t t y x mp_xy
  · exact cse1 C₀ σ r p q x y t t t z mp_xy
  · rw [LamI_exch]; exact cse21 C₀ σ r q p x t x y
  · rw [LamI_exch]; exact cse21 C₀ σ r q p x t z t
  · rw [LamI_exch]; exact cse21 C₀ σ r q p x t y x
  · rw [LamI_exch]; exact cse21 C₀ σ r q p x t t z
  · exact cse32 C₀ σ r p q x t z x y mq_tz
  · exact cse32 C₀ σ r p q x t z z t mq_tz
  · exact cse32 C₀ σ r p q x t z y x mq_tz
  · exact cse32 C₀ σ r p q x t z t z mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y x t x y mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y x t z t mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y x t y x mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y x t t z mq_xy
  · rw [LamI_swapE]; exact cse33 C₀ σ r p q x t y
  · rw [LamI_swapB, LamI_swapC]; exact cse33 C₀ σ r p q t x z
  · exact cse33 C₀ σ r p q x t y
  · rw [LamI_swapB, LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q t x z
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q x t z x y mq_tz
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q x t z z t mq_tz
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q x t z y x mq_tz
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q x t z t z mq_tz
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p z t x x y mq_tz
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p z t x z t mq_tz
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p z t x y x mq_tz
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p z t x t z mq_tz
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q t x z y x y mq_zt mq_xy
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q t x z y z t mq_zt mq_xy
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q t x z y y x mq_zt mq_xy
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q t x z y t z mq_zt mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t x t x y mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t x t z t mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t x t y x mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t x t t z mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x x t x y mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x x t z t mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x x t y x mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x x t t z mq_yx
  · exact cse31 C₀ σ r p q x t y z x y mq_yx mq_tz
  · exact cse31 C₀ σ r p q x t y z z t mq_yx mq_tz
  · exact cse31 C₀ σ r p q x t y z y x mq_yx mq_tz
  · exact cse31 C₀ σ r p q x t y z t z mq_yx mq_tz
  · rw [LamI_exch]; exact cse22 C₀ σ r q p y x t x y mq_xy
  · rw [LamI_exch]; exact cse22 C₀ σ r q p y x t z t mq_xy
  · rw [LamI_exch]; exact cse22 C₀ σ r q p y x t y x mq_xy
  · rw [LamI_exch]; exact cse22 C₀ σ r q p y x t t z mq_xy
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q t x y x y mq_xy
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q t x y z t mq_xy
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q t x y y x mq_xy
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q t x y t z mq_xy
  · rw [LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q x t y
  · rw [LamI_swapB]; exact cse33 C₀ σ r p q t x z
  · rw [LamI_swapC]; exact cse33 C₀ σ r p q x t y
  · rw [LamI_swapB, LamI_swapE]; exact cse33 C₀ σ r p q t x z
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z x t x y mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z x t z t mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z x t y x mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z x t t z mq_tz
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q t x y x y mq_xy
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q t x y z t mq_xy
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q t x y y x mq_xy
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q t x y t z mq_xy
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p t x x y
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p t x z t
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p t x y x
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p t x t z
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p x z x y
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p x z z t
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p x z y x
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p x z t z
  · rw [LamI_swapB, LamI_swapE]; exact cse33 C₀ σ r p q x z y
  · rw [LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q z x t
  · rw [LamI_swapB]; exact cse33 C₀ σ r p q x z y
  · rw [LamI_swapC]; exact cse33 C₀ σ r p q z x t
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y z x x y mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y z x z t mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y z x y x mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y z x t z mq_xy
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q x z t x y mq_zt
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q x z t z t mq_zt
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q x z t y x mq_zt
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q x z t t z mq_zt
  · rw [LamI_swapB, LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q x z y
  · rw [LamI_swapE]; exact cse33 C₀ σ r p q z x t
  · rw [LamI_swapB, LamI_swapC]; exact cse33 C₀ σ r p q x z y
  · exact cse33 C₀ σ r p q z x t
  · rw [LamI_exch]; exact cse21 C₀ σ r q p z x x y
  · rw [LamI_exch]; exact cse21 C₀ σ r q p z x z t
  · rw [LamI_exch]; exact cse21 C₀ σ r q p z x y x
  · rw [LamI_exch]; exact cse21 C₀ σ r q p z x t z
  · exact cse32 C₀ σ r p q z x y x y mq_xy
  · exact cse32 C₀ σ r p q z x y z t mq_xy
  · exact cse32 C₀ σ r p q z x y y x mq_xy
  · exact cse32 C₀ σ r p q z x y t z mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t z x x y mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t z x z t mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t z x y x mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t z x t z mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x z x x y mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x z x z t mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x z x y x mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x z x t z mq_yx
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q z x y x y mq_xy
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q z x y z t mq_xy
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q z x y y x mq_xy
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q z x y t z mq_xy
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p y x z x y mq_xy
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p y x z z t mq_xy
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p y x z y x mq_xy
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p y x z t z mq_xy
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q x z y t x y mq_yx mq_zt
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q x z y t z t mq_yx mq_zt
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q x z y t y x mq_yx mq_zt
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q x z y t t z mq_yx mq_zt
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q x z t x y mq_zt
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q x z t z t mq_zt
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q x z t y x mq_zt
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q x z t t z mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z z x x y mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z z x z t mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z z x y x mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z z x t z mq_tz
  · exact cse31 C₀ σ r p q z x t y x y mq_tz mq_xy
  · exact cse31 C₀ σ r p q z x t y z t mq_tz mq_xy
  · exact cse31 C₀ σ r p q z x t y y x mq_tz mq_xy
  · exact cse31 C₀ σ r p q z x t y t z mq_tz mq_xy
  · rw [LamI_exch]; exact cse22 C₀ σ r q p t z x x y mq_zt
  · rw [LamI_exch]; exact cse22 C₀ σ r q p t z x z t mq_zt
  · rw [LamI_exch]; exact cse22 C₀ σ r q p t z x y x mq_zt
  · rw [LamI_exch]; exact cse22 C₀ σ r q p t z x t z mq_zt
  · rw [LamI_swapE, LamI_exch]; exact cse23 C₀ σ r q p x z y lq_yx
  · rw [LamI_swapE]; exact cse23 C₀ σ r p q z x t lp_tz
  · rw [LamI_exch]; exact cse23 C₀ σ r q p x z y lq_yx
  · exact cse23 C₀ σ r p q z x t lp_tz
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q z x x y
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q z x z t
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q z x y x
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q z x t z
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y z z x y mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y z z z t mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y z z y x mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y z z t z mq_xy
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q z t x x y mp_tz
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q z t x z t mp_tz
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q z t x y x mp_tz
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q z t x t z mp_tz
  · exact cse21 C₀ σ r p q z x x y
  · exact cse21 C₀ σ r p q z x z t
  · exact cse21 C₀ σ r p q z x y x
  · exact cse21 C₀ σ r p q z x t z
  · exact cse21 C₀ σ r p q z z x y
  · exact cse21 C₀ σ r p q z z z t
  · exact cse21 C₀ σ r p q z z y x
  · exact cse21 C₀ σ r p q z z t z
  · exact cse21 C₀ σ r p q z y x y
  · exact cse21 C₀ σ r p q z y z t
  · exact cse21 C₀ σ r p q z y y x
  · exact cse21 C₀ σ r p q z y t z
  · exact cse21 C₀ σ r p q z t x y
  · exact cse21 C₀ σ r p q z t z t
  · exact cse21 C₀ σ r p q z t y x
  · exact cse21 C₀ σ r p q z t t z
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x z z x y mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x z z z t mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x z z y x mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x z z t z mq_yx
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q z y x y
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q z y z t
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q z y y x
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q z y t z
  · rw [LamI_exch]; exact cse23 C₀ σ r q p y z x lq_xy
  · rw [LamI_swapE]; exact cse23 C₀ σ r p q z y t lp_tz
  · rw [LamI_swapE, LamI_exch]; exact cse23 C₀ σ r q p y z x lq_xy
  · exact cse23 C₀ σ r p q z y t lp_tz
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q z t y x y mp_tz
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q z t y z t mp_tz
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q z t y y x mp_tz
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q z t y t z mp_tz
  · exact cse22 C₀ σ r p q z t x x y mp_tz
  · exact cse22 C₀ σ r p q z t x z t mp_tz
  · exact cse22 C₀ σ r p q z t x y x mp_tz
  · exact cse22 C₀ σ r p q z t x t z mp_tz
  · exact cse22 C₀ σ r p q z t z x y mp_tz
  · exact cse22 C₀ σ r p q z t z z t mp_tz
  · exact cse22 C₀ σ r p q z t z y x mp_tz
  · exact cse22 C₀ σ r p q z t z t z mp_tz
  · exact cse22 C₀ σ r p q z t y x y mp_tz
  · exact cse22 C₀ σ r p q z t y z t mp_tz
  · exact cse22 C₀ σ r p q z t y y x mp_tz
  · exact cse22 C₀ σ r p q z t y t z mp_tz
  · exact cse22 C₀ σ r p q z t t x y mp_tz
  · exact cse22 C₀ σ r p q z t t z t mp_tz
  · exact cse22 C₀ σ r p q z t t y x mp_tz
  · exact cse22 C₀ σ r p q z t t t z mp_tz
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p x y z x y mq_yx
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p x y z z t mq_yx
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p x y z y x mq_yx
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p x y z t z mq_yx
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q z y x x y mq_yx
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q z y x z t mq_yx
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q z y x y x mq_yx
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q z y x t z mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y z y x y mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y z y z t mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y z y y x mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y z y t z mq_xy
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q y z x t x y mq_xy mq_zt
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q y z x t z t mq_xy mq_zt
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q y z x t y x mq_xy mq_zt
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q y z x t t z mq_xy mq_zt
  · exact cse32 C₀ σ r p q z y x x y mq_yx
  · exact cse32 C₀ σ r p q z y x z t mq_yx
  · exact cse32 C₀ σ r p q z y x y x mq_yx
  · exact cse32 C₀ σ r p q z y x t z mq_yx
  · rw [LamI_exch]; exact cse21 C₀ σ r q p z y x y
  · rw [LamI_exch]; exact cse21 C₀ σ r q p z y z t
  · rw [LamI_exch]; exact cse21 C₀ σ r q p z y y x
  · rw [LamI_exch]; exact cse21 C₀ σ r q p z y t z
  · rw [LamI_swapB, LamI_swapC]; exact cse33 C₀ σ r p q y z x
  · rw [LamI_swapE]; exact cse33 C₀ σ r p q z y t
  · rw [LamI_swapB, LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q y z x
  · exact cse33 C₀ σ r p q z y t
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t z y x y mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t z y z t mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t z y y x mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t z y t z mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x z y x y mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x z y z t mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x z y y x mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x z y t z mq_yx
  · rw [LamI_swapB]; exact cse33 C₀ σ r p q y z x
  · rw [LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q z y t
  · rw [LamI_swapB, LamI_swapE]; exact cse33 C₀ σ r p q y z x
  · rw [LamI_swapC]; exact cse33 C₀ σ r p q z y t
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p y z x y
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p y z z t
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p y z y x
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p y z t z
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q y z t x y mq_zt
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q y z t z t mq_zt
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q y z t y x mq_zt
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q y z t t z mq_zt
  · exact cse31 C₀ σ r p q z y t x x y mq_tz mq_yx
  · exact cse31 C₀ σ r p q z y t x z t mq_tz mq_yx
  · exact cse31 C₀ σ r p q z y t x y x mq_tz mq_yx
  · exact cse31 C₀ σ r p q z y t x t z mq_tz mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z z y x y mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z z y z t mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z z y y x mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z z y t z mq_tz
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q y z t x y mq_zt
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q y z t z t mq_zt
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q y z t y x mq_zt
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q y z t t z mq_zt
  · rw [LamI_exch]; exact cse22 C₀ σ r q p t z y x y mq_zt
  · rw [LamI_exch]; exact cse22 C₀ σ r q p t z y z t mq_zt
  · rw [LamI_exch]; exact cse22 C₀ σ r q p t z y y x mq_zt
  · rw [LamI_exch]; exact cse22 C₀ σ r q p t z y t z mq_zt
  · exact cse1 C₀ σ r p q z t x x x y mp_zt
  · exact cse1 C₀ σ r p q z t x x z t mp_zt
  · exact cse1 C₀ σ r p q z t x x y x mp_zt
  · exact cse1 C₀ σ r p q z t x x t z mp_zt
  · exact cse1 C₀ σ r p q z t x z x y mp_zt
  · exact cse1 C₀ σ r p q z t x z z t mp_zt
  · exact cse1 C₀ σ r p q z t x z y x mp_zt
  · exact cse1 C₀ σ r p q z t x z t z mp_zt
  · exact cse1 C₀ σ r p q z t x y x y mp_zt
  · exact cse1 C₀ σ r p q z t x y z t mp_zt
  · exact cse1 C₀ σ r p q z t x y y x mp_zt
  · exact cse1 C₀ σ r p q z t x y t z mp_zt
  · exact cse1 C₀ σ r p q z t x t x y mp_zt
  · exact cse1 C₀ σ r p q z t x t z t mp_zt
  · exact cse1 C₀ σ r p q z t x t y x mp_zt
  · exact cse1 C₀ σ r p q z t x t t z mp_zt
  · exact cse1 C₀ σ r p q z t z x x y mp_zt
  · exact cse1 C₀ σ r p q z t z x z t mp_zt
  · exact cse1 C₀ σ r p q z t z x y x mp_zt
  · exact cse1 C₀ σ r p q z t z x t z mp_zt
  · exact cse1 C₀ σ r p q z t z z x y mp_zt
  · exact cse1 C₀ σ r p q z t z z z t mp_zt
  · exact cse1 C₀ σ r p q z t z z y x mp_zt
  · exact cse1 C₀ σ r p q z t z z t z mp_zt
  · exact cse1 C₀ σ r p q z t z y x y mp_zt
  · exact cse1 C₀ σ r p q z t z y z t mp_zt
  · exact cse1 C₀ σ r p q z t z y y x mp_zt
  · exact cse1 C₀ σ r p q z t z y t z mp_zt
  · exact cse1 C₀ σ r p q z t z t x y mp_zt
  · exact cse1 C₀ σ r p q z t z t z t mp_zt
  · exact cse1 C₀ σ r p q z t z t y x mp_zt
  · exact cse1 C₀ σ r p q z t z t t z mp_zt
  · exact cse1 C₀ σ r p q z t y x x y mp_zt
  · exact cse1 C₀ σ r p q z t y x z t mp_zt
  · exact cse1 C₀ σ r p q z t y x y x mp_zt
  · exact cse1 C₀ σ r p q z t y x t z mp_zt
  · exact cse1 C₀ σ r p q z t y z x y mp_zt
  · exact cse1 C₀ σ r p q z t y z z t mp_zt
  · exact cse1 C₀ σ r p q z t y z y x mp_zt
  · exact cse1 C₀ σ r p q z t y z t z mp_zt
  · exact cse1 C₀ σ r p q z t y y x y mp_zt
  · exact cse1 C₀ σ r p q z t y y z t mp_zt
  · exact cse1 C₀ σ r p q z t y y y x mp_zt
  · exact cse1 C₀ σ r p q z t y y t z mp_zt
  · exact cse1 C₀ σ r p q z t y t x y mp_zt
  · exact cse1 C₀ σ r p q z t y t z t mp_zt
  · exact cse1 C₀ σ r p q z t y t y x mp_zt
  · exact cse1 C₀ σ r p q z t y t t z mp_zt
  · exact cse1 C₀ σ r p q z t t x x y mp_zt
  · exact cse1 C₀ σ r p q z t t x z t mp_zt
  · exact cse1 C₀ σ r p q z t t x y x mp_zt
  · exact cse1 C₀ σ r p q z t t x t z mp_zt
  · exact cse1 C₀ σ r p q z t t z x y mp_zt
  · exact cse1 C₀ σ r p q z t t z z t mp_zt
  · exact cse1 C₀ σ r p q z t t z y x mp_zt
  · exact cse1 C₀ σ r p q z t t z t z mp_zt
  · exact cse1 C₀ σ r p q z t t y x y mp_zt
  · exact cse1 C₀ σ r p q z t t y z t mp_zt
  · exact cse1 C₀ σ r p q z t t y y x mp_zt
  · exact cse1 C₀ σ r p q z t t y t z mp_zt
  · exact cse1 C₀ σ r p q z t t t x y mp_zt
  · exact cse1 C₀ σ r p q z t t t z t mp_zt
  · exact cse1 C₀ σ r p q z t t t y x mp_zt
  · exact cse1 C₀ σ r p q z t t t t z mp_zt
  · exact cse1 C₀ σ r p q y x x x x y mp_yx
  · exact cse1 C₀ σ r p q y x x x z t mp_yx
  · exact cse1 C₀ σ r p q y x x x y x mp_yx
  · exact cse1 C₀ σ r p q y x x x t z mp_yx
  · exact cse1 C₀ σ r p q y x x z x y mp_yx
  · exact cse1 C₀ σ r p q y x x z z t mp_yx
  · exact cse1 C₀ σ r p q y x x z y x mp_yx
  · exact cse1 C₀ σ r p q y x x z t z mp_yx
  · exact cse1 C₀ σ r p q y x x y x y mp_yx
  · exact cse1 C₀ σ r p q y x x y z t mp_yx
  · exact cse1 C₀ σ r p q y x x y y x mp_yx
  · exact cse1 C₀ σ r p q y x x y t z mp_yx
  · exact cse1 C₀ σ r p q y x x t x y mp_yx
  · exact cse1 C₀ σ r p q y x x t z t mp_yx
  · exact cse1 C₀ σ r p q y x x t y x mp_yx
  · exact cse1 C₀ σ r p q y x x t t z mp_yx
  · exact cse1 C₀ σ r p q y x z x x y mp_yx
  · exact cse1 C₀ σ r p q y x z x z t mp_yx
  · exact cse1 C₀ σ r p q y x z x y x mp_yx
  · exact cse1 C₀ σ r p q y x z x t z mp_yx
  · exact cse1 C₀ σ r p q y x z z x y mp_yx
  · exact cse1 C₀ σ r p q y x z z z t mp_yx
  · exact cse1 C₀ σ r p q y x z z y x mp_yx
  · exact cse1 C₀ σ r p q y x z z t z mp_yx
  · exact cse1 C₀ σ r p q y x z y x y mp_yx
  · exact cse1 C₀ σ r p q y x z y z t mp_yx
  · exact cse1 C₀ σ r p q y x z y y x mp_yx
  · exact cse1 C₀ σ r p q y x z y t z mp_yx
  · exact cse1 C₀ σ r p q y x z t x y mp_yx
  · exact cse1 C₀ σ r p q y x z t z t mp_yx
  · exact cse1 C₀ σ r p q y x z t y x mp_yx
  · exact cse1 C₀ σ r p q y x z t t z mp_yx
  · exact cse1 C₀ σ r p q y x y x x y mp_yx
  · exact cse1 C₀ σ r p q y x y x z t mp_yx
  · exact cse1 C₀ σ r p q y x y x y x mp_yx
  · exact cse1 C₀ σ r p q y x y x t z mp_yx
  · exact cse1 C₀ σ r p q y x y z x y mp_yx
  · exact cse1 C₀ σ r p q y x y z z t mp_yx
  · exact cse1 C₀ σ r p q y x y z y x mp_yx
  · exact cse1 C₀ σ r p q y x y z t z mp_yx
  · exact cse1 C₀ σ r p q y x y y x y mp_yx
  · exact cse1 C₀ σ r p q y x y y z t mp_yx
  · exact cse1 C₀ σ r p q y x y y y x mp_yx
  · exact cse1 C₀ σ r p q y x y y t z mp_yx
  · exact cse1 C₀ σ r p q y x y t x y mp_yx
  · exact cse1 C₀ σ r p q y x y t z t mp_yx
  · exact cse1 C₀ σ r p q y x y t y x mp_yx
  · exact cse1 C₀ σ r p q y x y t t z mp_yx
  · exact cse1 C₀ σ r p q y x t x x y mp_yx
  · exact cse1 C₀ σ r p q y x t x z t mp_yx
  · exact cse1 C₀ σ r p q y x t x y x mp_yx
  · exact cse1 C₀ σ r p q y x t x t z mp_yx
  · exact cse1 C₀ σ r p q y x t z x y mp_yx
  · exact cse1 C₀ σ r p q y x t z z t mp_yx
  · exact cse1 C₀ σ r p q y x t z y x mp_yx
  · exact cse1 C₀ σ r p q y x t z t z mp_yx
  · exact cse1 C₀ σ r p q y x t y x y mp_yx
  · exact cse1 C₀ σ r p q y x t y z t mp_yx
  · exact cse1 C₀ σ r p q y x t y y x mp_yx
  · exact cse1 C₀ σ r p q y x t y t z mp_yx
  · exact cse1 C₀ σ r p q y x t t x y mp_yx
  · exact cse1 C₀ σ r p q y x t t z t mp_yx
  · exact cse1 C₀ σ r p q y x t t y x mp_yx
  · exact cse1 C₀ σ r p q y x t t t z mp_yx
  · rw [LamI_exch]; exact cse22 C₀ σ r q p x y z x y mq_yx
  · rw [LamI_exch]; exact cse22 C₀ σ r q p x y z z t mq_yx
  · rw [LamI_exch]; exact cse22 C₀ σ r q p x y z y x mq_yx
  · rw [LamI_exch]; exact cse22 C₀ σ r q p x y z t z mq_yx
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q z y x x y mq_yx
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q z y x z t mq_yx
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q z y x y x mq_yx
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q z y x t z mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y y z x y mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y y z z t mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y y z y x mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y y z t z mq_xy
  · exact cse31 C₀ σ r p q y z x t x y mq_xy mq_zt
  · exact cse31 C₀ σ r p q y z x t z t mq_xy mq_zt
  · exact cse31 C₀ σ r p q y z x t y x mq_xy mq_zt
  · exact cse31 C₀ σ r p q y z x t t z mq_xy mq_zt
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q z y x x y mq_yx
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q z y x z t mq_yx
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q z y x y x mq_yx
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q z y x t z mq_yx
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p z y x y
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p z y z t
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p z y y x
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p z y t z
  · rw [LamI_swapC]; exact cse33 C₀ σ r p q y z x
  · rw [LamI_swapB, LamI_swapE]; exact cse33 C₀ σ r p q z y t
  · rw [LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q y z x
  · rw [LamI_swapB]; exact cse33 C₀ σ r p q z y t
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t y z x y mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t y z z t mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t y z y x mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t y z t z mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x y z x y mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x y z z t mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x y z y x mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x y z t z mq_yx
  · exact cse33 C₀ σ r p q y z x
  · rw [LamI_swapB, LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q z y t
  · rw [LamI_swapE]; exact cse33 C₀ σ r p q y z x
  · rw [LamI_swapB, LamI_swapC]; exact cse33 C₀ σ r p q z y t
  · rw [LamI_exch]; exact cse21 C₀ σ r q p y z x y
  · rw [LamI_exch]; exact cse21 C₀ σ r q p y z z t
  · rw [LamI_exch]; exact cse21 C₀ σ r q p y z y x
  · rw [LamI_exch]; exact cse21 C₀ σ r q p y z t z
  · exact cse32 C₀ σ r p q y z t x y mq_zt
  · exact cse32 C₀ σ r p q y z t z t mq_zt
  · exact cse32 C₀ σ r p q y z t y x mq_zt
  · exact cse32 C₀ σ r p q y z t t z mq_zt
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q z y t x x y mq_tz mq_yx
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q z y t x z t mq_tz mq_yx
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q z y t x y x mq_tz mq_yx
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q z y t x t z mq_tz mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z y z x y mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z y z z t mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z y z y x mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z y z t z mq_tz
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q y z t x y mq_zt
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q y z t z t mq_zt
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q y z t y x mq_zt
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q y z t t z mq_zt
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p t z y x y mq_zt
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p t z y z t mq_zt
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p t z y y x mq_zt
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p t z y t z mq_zt
  · exact cse22 C₀ σ r p q y x x x y mp_xy
  · exact cse22 C₀ σ r p q y x x z t mp_xy
  · exact cse22 C₀ σ r p q y x x y x mp_xy
  · exact cse22 C₀ σ r p q y x x t z mp_xy
  · exact cse22 C₀ σ r p q y x z x y mp_xy
  · exact cse22 C₀ σ r p q y x z z t mp_xy
  · exact cse22 C₀ σ r p q y x z y x mp_xy
  · exact cse22 C₀ σ r p q y x z t z mp_xy
  · exact cse22 C₀ σ r p q y x y x y mp_xy
  · exact cse22 C₀ σ r p q y x y z t mp_xy
  · exact cse22 C₀ σ r p q y x y y x mp_xy
  · exact cse22 C₀ σ r p q y x y t z mp_xy
  · exact cse22 C₀ σ r p q y x t x y mp_xy
  · exact cse22 C₀ σ r p q y x t z t mp_xy
  · exact cse22 C₀ σ r p q y x t y x mp_xy
  · exact cse22 C₀ σ r p q y x t t z mp_xy
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q y x z x y mp_xy
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q y x z z t mp_xy
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q y x z y x mp_xy
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q y x z t z mp_xy
  · exact cse23 C₀ σ r p q y z x lp_xy
  · rw [LamI_swapE, LamI_exch]; exact cse23 C₀ σ r q p z y t lq_tz
  · rw [LamI_swapE]; exact cse23 C₀ σ r p q y z x lp_xy
  · rw [LamI_exch]; exact cse23 C₀ σ r q p z y t lq_tz
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q y z x y
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q y z z t
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q y z y x
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q y z t z
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t y y x y mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t y y z t mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t y y y x mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t y y t z mq_zt
  · exact cse21 C₀ σ r p q y x x y
  · exact cse21 C₀ σ r p q y x z t
  · exact cse21 C₀ σ r p q y x y x
  · exact cse21 C₀ σ r p q y x t z
  · exact cse21 C₀ σ r p q y z x y
  · exact cse21 C₀ σ r p q y z z t
  · exact cse21 C₀ σ r p q y z y x
  · exact cse21 C₀ σ r p q y z t z
  · exact cse21 C₀ σ r p q y y x y
  · exact cse21 C₀ σ r p q y y z t
  · exact cse21 C₀ σ r p q y y y x
  · exact cse21 C₀ σ r p q y y t z
  · exact cse21 C₀ σ r p q y t x y
  · exact cse21 C₀ σ r p q y t z t
  · exact cse21 C₀ σ r p q y t y x
  · exact cse21 C₀ σ r p q y t t z
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q y x t x y mp_xy
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q y x t z t mp_xy
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q y x t y x mp_xy
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q y x t t z mp_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z y y x y mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z y y z t mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z y y y x mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z y y t z mq_tz
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q y t x y
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q y t z t
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q y t y x
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q y t t z
  · exact cse23 C₀ σ r p q y t x lp_xy
  · rw [LamI_exch]; exact cse23 C₀ σ r q p t y z lq_zt
  · rw [LamI_swapE]; exact cse23 C₀ σ r p q y t x lp_xy
  · rw [LamI_swapE, LamI_exch]; exact cse23 C₀ σ r q p t y z lq_zt
  · rw [LamI_exch]; exact cse22 C₀ σ r q p x y t x y mq_yx
  · rw [LamI_exch]; exact cse22 C₀ σ r q p x y t z t mq_yx
  · rw [LamI_exch]; exact cse22 C₀ σ r q p x y t y x mq_yx
  · rw [LamI_exch]; exact cse22 C₀ σ r q p x y t t z mq_yx
  · exact cse31 C₀ σ r p q y t x z x y mq_xy mq_tz
  · exact cse31 C₀ σ r p q y t x z z t mq_xy mq_tz
  · exact cse31 C₀ σ r p q y t x z y x mq_xy mq_tz
  · exact cse31 C₀ σ r p q y t x z t z mq_xy mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y y t x y mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y y t z t mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y y t y x mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y y t t z mq_xy
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q t y x x y mq_yx
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q t y x z t mq_yx
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q t y x y x mq_yx
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q t y x t z mq_yx
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q t y z x x y mq_zt mq_yx
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q t y z x z t mq_zt mq_yx
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q t y z x y x mq_zt mq_yx
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q t y z x t z mq_zt mq_yx
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p z t y x y mq_tz
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p z t y z t mq_tz
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p z t y y x mq_tz
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p z t y t z mq_tz
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q y t z x y mq_tz
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q y t z z t mq_tz
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q y t z y x mq_tz
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q y t z t z mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t y t x y mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t y t z t mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t y t y x mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t y t t z mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x y t x y mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x y t z t mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x y t y x mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x y t t z mq_yx
  · exact cse32 C₀ σ r p q y t z x y mq_tz
  · exact cse32 C₀ σ r p q y t z z t mq_tz
  · exact cse32 C₀ σ r p q y t z y x mq_tz
  · exact cse32 C₀ σ r p q y t z t z mq_tz
  · rw [LamI_exch]; exact cse21 C₀ σ r q p y t x y
  · rw [LamI_exch]; exact cse21 C₀ σ r q p y t z t
  · rw [LamI_exch]; exact cse21 C₀ σ r q p y t y x
  · rw [LamI_exch]; exact cse21 C₀ σ r q p y t t z
  · exact cse33 C₀ σ r p q y t x
  · rw [LamI_swapB, LamI_swapC]; exact cse33 C₀ σ r p q t y z
  · rw [LamI_swapE]; exact cse33 C₀ σ r p q y t x
  · rw [LamI_swapB, LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q t y z
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q t y x x y mq_yx
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q t y x z t mq_yx
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q t y x y x mq_yx
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q t y x t z mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z y t x y mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z y t z t mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z y t y x mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z y t t z mq_tz
  · rw [LamI_swapC]; exact cse33 C₀ σ r p q y t x
  · rw [LamI_swapB]; exact cse33 C₀ σ r p q t y z
  · rw [LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q y t x
  · rw [LamI_swapB, LamI_swapE]; exact cse33 C₀ σ r p q t y z
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p t y x y
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p t y z t
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p t y y x
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p t y t z
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p x t x y
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p x t z t
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p x t y x
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p x t t z
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q x t z x y mq_tz
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q x t z z t mq_tz
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q x t z y x mq_tz
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q x t z t z mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y t x x y mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y t x z t mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y t x y x mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y t x t z mq_xy
  · rw [LamI_swapB, LamI_swapE]; exact cse33 C₀ σ r p q x t y
  · rw [LamI_swapC]; exact cse33 C₀ σ r p q t x z
  · rw [LamI_swapB]; exact cse33 C₀ σ r p q x t y
  · rw [LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q t x z
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q x t z x y mq_tz
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q x t z z t mq_tz
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q x t z y x mq_tz
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q x t z t z mq_tz
  · rw [LamI_exch]; exact cse22 C₀ σ r q p z t x x y mq_tz
  · rw [LamI_exch]; exact cse22 C₀ σ r q p z t x z t mq_tz
  · rw [LamI_exch]; exact cse22 C₀ σ r q p z t x y x mq_tz
  · rw [LamI_exch]; exact cse22 C₀ σ r q p z t x t z mq_tz
  · exact cse31 C₀ σ r p q t x z y x y mq_zt mq_xy
  · exact cse31 C₀ σ r p q t x z y z t mq_zt mq_xy
  · exact cse31 C₀ σ r p q t x z y y x mq_zt mq_xy
  · exact cse31 C₀ σ r p q t x z y t z mq_zt mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t t x x y mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t t x z t mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t t x y x mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t t x t z mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x t x x y mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x t x z t mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x t x y x mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x t x t z mq_yx
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q x t y z x y mq_yx mq_tz
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q x t y z z t mq_yx mq_tz
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q x t y z y x mq_yx mq_tz
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q x t y z t z mq_yx mq_tz
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p y x t x y mq_xy
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p y x t z t mq_xy
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p y x t y x mq_xy
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p y x t t z mq_xy
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q t x y x y mq_xy
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q t x y z t mq_xy
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q t x y y x mq_xy
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q t x y t z mq_xy
  · rw [LamI_swapB, LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q x t y
  · exact cse33 C₀ σ r p q t x z
  · rw [LamI_swapB, LamI_swapC]; exact cse33 C₀ σ r p q x t y
  · rw [LamI_swapE]; exact cse33 C₀ σ r p q t x z
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z t x x y mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z t x z t mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z t x y x mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z t x t z mq_tz
  · exact cse32 C₀ σ r p q t x y x y mq_xy
  · exact cse32 C₀ σ r p q t x y z t mq_xy
  · exact cse32 C₀ σ r p q t x y y x mq_xy
  · exact cse32 C₀ σ r p q t x y t z mq_xy
  · rw [LamI_exch]; exact cse21 C₀ σ r q p t x x y
  · rw [LamI_exch]; exact cse21 C₀ σ r q p t x z t
  · rw [LamI_exch]; exact cse21 C₀ σ r q p t x y x
  · rw [LamI_exch]; exact cse21 C₀ σ r q p t x t z
  · exact cse1 C₀ σ r p q t z x x x y mp_tz
  · exact cse1 C₀ σ r p q t z x x z t mp_tz
  · exact cse1 C₀ σ r p q t z x x y x mp_tz
  · exact cse1 C₀ σ r p q t z x x t z mp_tz
  · exact cse1 C₀ σ r p q t z x z x y mp_tz
  · exact cse1 C₀ σ r p q t z x z z t mp_tz
  · exact cse1 C₀ σ r p q t z x z y x mp_tz
  · exact cse1 C₀ σ r p q t z x z t z mp_tz
  · exact cse1 C₀ σ r p q t z x y x y mp_tz
  · exact cse1 C₀ σ r p q t z x y z t mp_tz
  · exact cse1 C₀ σ r p q t z x y y x mp_tz
  · exact cse1 C₀ σ r p q t z x y t z mp_tz
  · exact cse1 C₀ σ r p q t z x t x y mp_tz
  · exact cse1 C₀ σ r p q t z x t z t mp_tz
  · exact cse1 C₀ σ r p q t z x t y x mp_tz
  · exact cse1 C₀ σ r p q t z x t t z mp_tz
  · exact cse1 C₀ σ r p q t z z x x y mp_tz
  · exact cse1 C₀ σ r p q t z z x z t mp_tz
  · exact cse1 C₀ σ r p q t z z x y x mp_tz
  · exact cse1 C₀ σ r p q t z z x t z mp_tz
  · exact cse1 C₀ σ r p q t z z z x y mp_tz
  · exact cse1 C₀ σ r p q t z z z z t mp_tz
  · exact cse1 C₀ σ r p q t z z z y x mp_tz
  · exact cse1 C₀ σ r p q t z z z t z mp_tz
  · exact cse1 C₀ σ r p q t z z y x y mp_tz
  · exact cse1 C₀ σ r p q t z z y z t mp_tz
  · exact cse1 C₀ σ r p q t z z y y x mp_tz
  · exact cse1 C₀ σ r p q t z z y t z mp_tz
  · exact cse1 C₀ σ r p q t z z t x y mp_tz
  · exact cse1 C₀ σ r p q t z z t z t mp_tz
  · exact cse1 C₀ σ r p q t z z t y x mp_tz
  · exact cse1 C₀ σ r p q t z z t t z mp_tz
  · exact cse1 C₀ σ r p q t z y x x y mp_tz
  · exact cse1 C₀ σ r p q t z y x z t mp_tz
  · exact cse1 C₀ σ r p q t z y x y x mp_tz
  · exact cse1 C₀ σ r p q t z y x t z mp_tz
  · exact cse1 C₀ σ r p q t z y z x y mp_tz
  · exact cse1 C₀ σ r p q t z y z z t mp_tz
  · exact cse1 C₀ σ r p q t z y z y x mp_tz
  · exact cse1 C₀ σ r p q t z y z t z mp_tz
  · exact cse1 C₀ σ r p q t z y y x y mp_tz
  · exact cse1 C₀ σ r p q t z y y z t mp_tz
  · exact cse1 C₀ σ r p q t z y y y x mp_tz
  · exact cse1 C₀ σ r p q t z y y t z mp_tz
  · exact cse1 C₀ σ r p q t z y t x y mp_tz
  · exact cse1 C₀ σ r p q t z y t z t mp_tz
  · exact cse1 C₀ σ r p q t z y t y x mp_tz
  · exact cse1 C₀ σ r p q t z y t t z mp_tz
  · exact cse1 C₀ σ r p q t z t x x y mp_tz
  · exact cse1 C₀ σ r p q t z t x z t mp_tz
  · exact cse1 C₀ σ r p q t z t x y x mp_tz
  · exact cse1 C₀ σ r p q t z t x t z mp_tz
  · exact cse1 C₀ σ r p q t z t z x y mp_tz
  · exact cse1 C₀ σ r p q t z t z z t mp_tz
  · exact cse1 C₀ σ r p q t z t z y x mp_tz
  · exact cse1 C₀ σ r p q t z t z t z mp_tz
  · exact cse1 C₀ σ r p q t z t y x y mp_tz
  · exact cse1 C₀ σ r p q t z t y z t mp_tz
  · exact cse1 C₀ σ r p q t z t y y x mp_tz
  · exact cse1 C₀ σ r p q t z t y t z mp_tz
  · exact cse1 C₀ σ r p q t z t t x y mp_tz
  · exact cse1 C₀ σ r p q t z t t z t mp_tz
  · exact cse1 C₀ σ r p q t z t t y x mp_tz
  · exact cse1 C₀ σ r p q t z t t t z mp_tz
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p x y t x y mq_yx
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p x y t z t mq_yx
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p x y t y x mq_yx
  · rw [LamI_swapB, LamI_exch]; exact cse22 C₀ σ r q p x y t t z mq_yx
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q y t x z x y mq_xy mq_tz
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q y t x z z t mq_xy mq_tz
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q y t x z y x mq_xy mq_tz
  · rw [LamI_swapB]; exact cse31 C₀ σ r p q y t x z t z mq_xy mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y t y x y mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y t y z t mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y t y y x mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y t y t z mq_xy
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q t y x x y mq_yx
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q t y x z t mq_yx
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q t y x y x mq_yx
  · rw [LamI_swapC]; exact cse32 C₀ σ r p q t y x t z mq_yx
  · exact cse31 C₀ σ r p q t y z x x y mq_zt mq_yx
  · exact cse31 C₀ σ r p q t y z x z t mq_zt mq_yx
  · exact cse31 C₀ σ r p q t y z x y x mq_zt mq_yx
  · exact cse31 C₀ σ r p q t y z x t z mq_zt mq_yx
  · rw [LamI_exch]; exact cse22 C₀ σ r q p z t y x y mq_tz
  · rw [LamI_exch]; exact cse22 C₀ σ r q p z t y z t mq_tz
  · rw [LamI_exch]; exact cse22 C₀ σ r q p z t y y x mq_tz
  · rw [LamI_exch]; exact cse22 C₀ σ r q p z t y t z mq_tz
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q y t z x y mq_tz
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q y t z z t mq_tz
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q y t z y x mq_tz
  · rw [LamI_swapB, LamI_swapC]; exact cse32 C₀ σ r p q y t z t z mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t t y x y mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t t y z t mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t t y y x mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p z t t y t z mq_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x t y x y mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x t y z t mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x t y y x mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x t y t z mq_yx
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q y t z x y mq_tz
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q y t z z t mq_tz
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q y t z y x mq_tz
  · rw [LamI_swapB]; exact cse32 C₀ σ r p q y t z t z mq_tz
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p y t x y
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p y t z t
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p y t y x
  · rw [LamI_swapB, LamI_exch]; exact cse21 C₀ σ r q p y t t z
  · rw [LamI_swapB]; exact cse33 C₀ σ r p q y t x
  · rw [LamI_swapC]; exact cse33 C₀ σ r p q t y z
  · rw [LamI_swapB, LamI_swapE]; exact cse33 C₀ σ r p q y t x
  · rw [LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q t y z
  · exact cse32 C₀ σ r p q t y x x y mq_yx
  · exact cse32 C₀ σ r p q t y x z t mq_yx
  · exact cse32 C₀ σ r p q t y x y x mq_yx
  · exact cse32 C₀ σ r p q t y x t z mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z t y x y mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z t y z t mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z t y y x mq_tz
  · rw [LamI_exch]; exact cse1 C₀ σ r q p t z t y t z mq_tz
  · rw [LamI_swapB, LamI_swapC]; exact cse33 C₀ σ r p q y t x
  · exact cse33 C₀ σ r p q t y z
  · rw [LamI_swapB, LamI_swapC, LamI_swapE]; exact cse33 C₀ σ r p q y t x
  · rw [LamI_swapE]; exact cse33 C₀ σ r p q t y z
  · rw [LamI_exch]; exact cse21 C₀ σ r q p t y x y
  · rw [LamI_exch]; exact cse21 C₀ σ r q p t y z t
  · rw [LamI_exch]; exact cse21 C₀ σ r q p t y y x
  · rw [LamI_exch]; exact cse21 C₀ σ r q p t y t z
  · rw [LamI_swapE, LamI_exch]; exact cse23 C₀ σ r q p x t y lq_yx
  · exact cse23 C₀ σ r p q t x z lp_zt
  · rw [LamI_exch]; exact cse23 C₀ σ r q p x t y lq_yx
  · rw [LamI_swapE]; exact cse23 C₀ σ r p q t x z lp_zt
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q t z x x y mp_zt
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q t z x z t mp_zt
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q t z x y x mp_zt
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q t z x t z mp_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y t t x y mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y t t z t mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y t t y x mq_xy
  · rw [LamI_exch]; exact cse1 C₀ σ r q p x y t t t z mq_xy
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q t x x y
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q t x z t
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q t x y x
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q t x t z
  · exact cse22 C₀ σ r p q t z x x y mp_zt
  · exact cse22 C₀ σ r p q t z x z t mp_zt
  · exact cse22 C₀ σ r p q t z x y x mp_zt
  · exact cse22 C₀ σ r p q t z x t z mp_zt
  · exact cse22 C₀ σ r p q t z z x y mp_zt
  · exact cse22 C₀ σ r p q t z z z t mp_zt
  · exact cse22 C₀ σ r p q t z z y x mp_zt
  · exact cse22 C₀ σ r p q t z z t z mp_zt
  · exact cse22 C₀ σ r p q t z y x y mp_zt
  · exact cse22 C₀ σ r p q t z y z t mp_zt
  · exact cse22 C₀ σ r p q t z y y x mp_zt
  · exact cse22 C₀ σ r p q t z y t z mp_zt
  · exact cse22 C₀ σ r p q t z t x y mp_zt
  · exact cse22 C₀ σ r p q t z t z t mp_zt
  · exact cse22 C₀ σ r p q t z t y x mp_zt
  · exact cse22 C₀ σ r p q t z t t z mp_zt
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x t t x y mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x t t z t mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x t t y x mq_yx
  · rw [LamI_exch]; exact cse1 C₀ σ r q p y x t t t z mq_yx
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q t z y x y mp_zt
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q t z y z t mp_zt
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q t z y y x mp_zt
  · rw [LamI_swapC]; exact cse22 C₀ σ r p q t z y t z mp_zt
  · rw [LamI_exch]; exact cse23 C₀ σ r q p y t x lq_xy
  · exact cse23 C₀ σ r p q t y z lp_zt
  · rw [LamI_swapE, LamI_exch]; exact cse23 C₀ σ r q p y t x lq_xy
  · rw [LamI_swapE]; exact cse23 C₀ σ r p q t y z lp_zt
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q t y x y
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q t y z t
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q t y y x
  · rw [LamI_swapC]; exact cse21 C₀ σ r p q t y t z
  · exact cse21 C₀ σ r p q t x x y
  · exact cse21 C₀ σ r p q t x z t
  · exact cse21 C₀ σ r p q t x y x
  · exact cse21 C₀ σ r p q t x t z
  · exact cse21 C₀ σ r p q t z x y
  · exact cse21 C₀ σ r p q t z z t
  · exact cse21 C₀ σ r p q t z y x
  · exact cse21 C₀ σ r p q t z t z
  · exact cse21 C₀ σ r p q t y x y
  · exact cse21 C₀ σ r p q t y z t
  · exact cse21 C₀ σ r p q t y y x
  · exact cse21 C₀ σ r p q t y t z
  · exact cse21 C₀ σ r p q t t x y
  · exact cse21 C₀ σ r p q t t z t
  · exact cse21 C₀ σ r p q t t y x
  · exact cse21 C₀ σ r p q t t t z
