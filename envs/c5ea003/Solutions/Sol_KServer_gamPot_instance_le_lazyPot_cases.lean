-- Prove2me | solution 1 for KServer.gamPot_instance_le_lazyPot_cases
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T18:42:42.754334+00:00
-- url     : https://prove2.me/submissions/e9ef6ef1-3cbf-495f-95f9-9fa40d81f933

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_quasiconvex_three
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_lazyPot_ge_instance

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

section GamCases
variable {M : Type} [MetricSpace M] (C₀ : Config 3 M) (σ : List M) (r : M)

/-- Case 1 with the quasiconvexity branch fixed. -/
private theorem gaux1 (p q b b' d' f : M)
    (hQ : workFnU C₀ σ ![r, b, q] + workFnU C₀ σ ![r, f, b']
      ≤ workFnU C₀ σ ![r, b, b'] + workFnU C₀ σ ![r, q, f]) :
    (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
      + dist r q + dist f d' - workFnU C₀ σ ![r, q, f] - workFnU C₀ σ ![r, q, d']
      + dist q f - workFnU C₀ σ ![r, p, f]
      ≤ lazyPot C₀ σ r := by
  have hI := lazyPot_ge_instance M C₀ σ r b q f q d' b' p
  have t1 : dist p b ≤ dist p r + dist r b := dist_triangle p r b
  have hc1 : dist p r = dist r p := dist_comm p r
  have hc2 : dist f q = dist q f := dist_comm f q
  have hc3 : dist b' p = dist p b' := dist_comm b' p
  have s1 : workFnU C₀ σ ![r, f, b'] = workFnU C₀ σ ![r, b', f] := swap12 C₀ σ r f b'
  have s2 : workFnU C₀ σ ![r, f, p] = workFnU C₀ σ ![r, p, f] := swap12 C₀ σ r f p
  have s3 : workFnU C₀ σ ![r, b, q] = workFnU C₀ σ ![r, q, b] := swap12 C₀ σ r b q
  linarith

/-- Case 4.2 with the quasiconvexity branch fixed. -/
private theorem gaux42 (p q b b' d : M)
    (hQ : workFnU C₀ σ ![r, q, b'] + workFnU C₀ σ ![r, d, p]
      ≤ workFnU C₀ σ ![r, q, d] + workFnU C₀ σ ![r, p, b']) :
    (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
      + dist r q + dist d b - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, b]
      + dist q b' - workFnU C₀ σ ![r, p, b']
      ≤ lazyPot C₀ σ r := by
  have hI := lazyPot_ge_instance M C₀ σ r q b' b p d q b'
  have t1 : dist p b' ≤ dist p r + dist r b' := dist_triangle p r b'
  have hc1 : dist p r = dist r p := dist_comm p r
  have hc2 : dist b p = dist p b := dist_comm b p
  have hc3 : dist b d = dist d b := dist_comm b d
  have s1 : workFnU C₀ σ ![r, b, q] = workFnU C₀ σ ![r, q, b] := swap12 C₀ σ r b q
  have s2 : workFnU C₀ σ ![r, p, d] = workFnU C₀ σ ![r, d, p] := swap12 C₀ σ r p d
  have s3 : workFnU C₀ σ ![r, q, b'] = workFnU C₀ σ ![r, b', q] := swap12 C₀ σ r q b'
  linarith

end GamCases

section GamMore
variable {M : Type} [MetricSpace M] (C₀ : Config 3 M) (σ : List M) (r : M)

/-- Case 4.2, the other quasiconvexity branch. -/
private theorem gaux42b (p q b b' d : M)
    (hQ : workFnU C₀ σ ![r, q, p] + workFnU C₀ σ ![r, d, b']
      ≤ workFnU C₀ σ ![r, q, d] + workFnU C₀ σ ![r, p, b']) :
    (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
      + dist r q + dist d b - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, b]
      + dist q b' - workFnU C₀ σ ![r, p, b']
      ≤ lazyPot C₀ σ r := by
  have hI := lazyPot_ge_instance M C₀ σ r b q b' p q d b
  have t1 : dist p b ≤ dist p r + dist r b := dist_triangle p r b
  have hc1 : dist p r = dist r p := dist_comm p r
  have hc2 : dist b' p = dist p b' := dist_comm b' p
  have hc3 : dist b' q = dist q b' := dist_comm b' q
  have s1 : workFnU C₀ σ ![r, b, q] = workFnU C₀ σ ![r, q, b] := swap12 C₀ σ r b q
  have s2 : workFnU C₀ σ ![r, p, q] = workFnU C₀ σ ![r, q, p] := swap12 C₀ σ r p q
  have s3 : workFnU C₀ σ ![r, b', d] = workFnU C₀ σ ![r, d, b'] := swap12 C₀ σ r b' d
  have s4 : workFnU C₀ σ ![r, b', b] = workFnU C₀ σ ![r, b, b'] := swap12 C₀ σ r b' b
  linarith

/-- Case 3.2, first quasiconvexity branch. -/
private theorem gaux32a (p q b d d' : M)
    (hcol : dist q p + dist q b = dist p b)
    (hQ : workFnU C₀ σ ![r, p, d] + workFnU C₀ σ ![r, b, q]
      ≤ workFnU C₀ σ ![r, p, b] + workFnU C₀ σ ![r, q, d]) :
    (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
      + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
      + dist q b - workFnU C₀ σ ![r, p, b]
      ≤ lazyPot C₀ σ r := by
  have hI := lazyPot_ge_instance M C₀ σ r b q p b b d d'
  have t1 : dist p b ≤ dist p r + dist r b := dist_triangle p r b
  have hc1 : dist p r = dist r p := dist_comm p r
  have l1 : workFnU C₀ σ ![r, p, d'] ≤ workFnU C₀ σ ![r, q, d'] + dist q p := lipP C₀ σ r p q d'
  have s1 : workFnU C₀ σ ![r, b, q] = workFnU C₀ σ ![r, q, b] := swap12 C₀ σ r b q
  linarith

/-- Case 3.2, second quasiconvexity branch. -/
private theorem gaux32b (p q b d d' : M)
    (hcol : dist q p + dist q b = dist p b)
    (hQ : workFnU C₀ σ ![r, p, q] + workFnU C₀ σ ![r, b, d]
      ≤ workFnU C₀ σ ![r, p, b] + workFnU C₀ σ ![r, q, d]) :
    (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
      + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
      + dist q b - workFnU C₀ σ ![r, p, b]
      ≤ lazyPot C₀ σ r := by
  have hI := lazyPot_ge_instance M C₀ σ r b q b p p d d'
  have t1 : dist p b ≤ dist p r + dist r b := dist_triangle p r b
  have hc1 : dist p r = dist r p := dist_comm p r
  have hc2 : dist b p = dist p b := dist_comm b p
  have l1 : workFnU C₀ σ ![r, p, p] ≤ workFnU C₀ σ ![r, q, p] + dist q p := lipP C₀ σ r p q p
  have hq2 := workFnU_quasiconvex_three M C₀ σ r b b q d'
  rw [min_eq_left (le_of_eq (by ring))] at hq2
  have s1 : workFnU C₀ σ ![r, b, q] = workFnU C₀ σ ![r, q, b] := swap12 C₀ σ r b q
  have s2 : workFnU C₀ σ ![r, q, p] = workFnU C₀ σ ![r, p, q] := swap12 C₀ σ r q p
  linarith

/-- Case 3.1: an average of two instances. -/
private theorem gaux31 (p q b d d' : M) :
    (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
      + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
      + dist q p - workFnU C₀ σ ![r, p, p]
      ≤ lazyPot C₀ σ r := by
  have hI1 := lazyPot_ge_instance M C₀ σ r b q b p p d d'
  have hI2 := lazyPot_ge_instance M C₀ σ r b q q p p d d'
  have t1 : dist p b ≤ dist p r + dist r b := dist_triangle p r b
  have hc1 : dist p r = dist r p := dist_comm p r
  have hc2 : dist b p = dist p b := dist_comm b p
  have hc3 : dist q p = dist q p := rfl
  have hq1 := workFnU_quasiconvex_three M C₀ σ r b b q d
  rw [min_eq_left (le_of_eq (by ring))] at hq1
  have hq2 := workFnU_quasiconvex_three M C₀ σ r b b q d'
  rw [min_eq_left (le_of_eq (by ring))] at hq2
  linarith

/-- The reduction of Case 3: the point `p` may be moved to the far corner. -/
private theorem gaux3red (p X q b d d' f : M) (hcol : dist X p + dist p b = dist X b) :
    (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
      + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
      + dist q f - workFnU C₀ σ ![r, p, f]
      ≤ (-dist r X + (dist X b + dist X b - workFnU C₀ σ ![r, b, b]))
      + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
      + dist q f - workFnU C₀ σ ![r, X, f] := by
  have t1 : dist r X ≤ dist r p + dist p X := dist_triangle r p X
  have l1 : workFnU C₀ σ ![r, X, f] ≤ workFnU C₀ σ ![r, p, f] + dist p X := lipP C₀ σ r X p f
  have hc : dist p X = dist X p := dist_comm p X
  linarith

/-- Case 3.3.1. -/
private theorem gaux331 (p q b f : M) :
    (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
      + dist r q + dist p b - workFnU C₀ σ ![r, q, p] - workFnU C₀ σ ![r, q, b]
      + dist q f - workFnU C₀ σ ![r, p, f]
      ≤ lazyPot C₀ σ r := by
  have hI := lazyPot_ge_instance M C₀ σ r b q p b b q f
  have t1 : dist p b ≤ dist p r + dist r b := dist_triangle p r b
  have hc1 : dist p r = dist r p := dist_comm p r
  have s1 : workFnU C₀ σ ![r, b, q] = workFnU C₀ σ ![r, q, b] := swap12 C₀ σ r b q
  have s2 : workFnU C₀ σ ![r, p, q] = workFnU C₀ σ ![r, q, p] := swap12 C₀ σ r p q
  linarith

/-- Case 4.1. -/
private theorem gaux41 (p q b b' d f : M) (hcol : dist q b' + dist q f = dist b' f) :
    (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
      + dist r q + dist d b - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, b]
      + dist q f - workFnU C₀ σ ![r, p, f]
      ≤ lazyPot C₀ σ r := by
  have hI := lazyPot_ge_instance M C₀ σ r b q b' f p d b
  have t1 : dist p b ≤ dist p r + dist r b := dist_triangle p r b
  have hc1 : dist p r = dist r p := dist_comm p r
  have hc2 : dist b' p = dist p b' := dist_comm b' p
  have l1 : workFnU C₀ σ ![r, b', d] ≤ workFnU C₀ σ ![r, q, d] + dist q b' := lipP C₀ σ r b' q d
  have s1 : workFnU C₀ σ ![r, b, q] = workFnU C₀ σ ![r, q, b] := swap12 C₀ σ r b q
  have s2 : workFnU C₀ σ ![r, f, p] = workFnU C₀ σ ![r, p, f] := swap12 C₀ σ r f p
  have s3 : workFnU C₀ σ ![r, b', b] = workFnU C₀ σ ![r, b, b'] := swap12 C₀ σ r b' b
  linarith

/-- Case 2. -/
private theorem gaux2 (p q b b' d d' f : M)
    (hp : dist p b + dist p b' = dist b b') (hr : dist r b + dist r b' = dist b b') :
    (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
      + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
      + dist q f - workFnU C₀ σ ![r, p, f]
      ≤ lazyPot C₀ σ r := by
  have hI := lazyPot_ge_instance M C₀ σ r b b' q f p d d'
  have t1 : dist r q ≤ dist r p + dist p q := dist_triangle r p q
  have hc1 : dist q p = dist p q := dist_comm q p
  have s1 : workFnU C₀ σ ![r, f, p] = workFnU C₀ σ ![r, p, f] := swap12 C₀ σ r f p
  linarith

end GamMore

/-- **The configuration lemmas for the auxiliary potential `Γ`.** -/
theorem solution (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M) (r : M) :
    (∀ p q b b' d' f : M,
      (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
        + dist r q + dist f d' - workFnU C₀ σ ![r, q, f] - workFnU C₀ σ ![r, q, d']
        + dist q f - workFnU C₀ σ ![r, p, f] ≤ lazyPot C₀ σ r)
    ∧ (∀ p q b b' d d' f : M, dist p b + dist p b' = dist b b' →
        dist r b + dist r b' = dist b b' →
      (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
        + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
        + dist q f - workFnU C₀ σ ![r, p, f] ≤ lazyPot C₀ σ r)
    ∧ (∀ p X q b d d' f : M, dist X p + dist p b = dist X b →
      (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
        + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
        + dist q f - workFnU C₀ σ ![r, p, f]
        ≤ (-dist r X + (dist X b + dist X b - workFnU C₀ σ ![r, b, b]))
        + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
        + dist q f - workFnU C₀ σ ![r, X, f])
    ∧ (∀ p q b d d' : M,
      (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
        + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
        + dist q p - workFnU C₀ σ ![r, p, p] ≤ lazyPot C₀ σ r)
    ∧ (∀ p q b d d' : M, dist q p + dist q b = dist p b →
      (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
        + dist r q + dist d d' - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, d']
        + dist q b - workFnU C₀ σ ![r, p, b] ≤ lazyPot C₀ σ r)
    ∧ (∀ p q b f : M,
      (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
        + dist r q + dist p b - workFnU C₀ σ ![r, q, p] - workFnU C₀ σ ![r, q, b]
        + dist q f - workFnU C₀ σ ![r, p, f] ≤ lazyPot C₀ σ r)
    ∧ (∀ p q b b' d f : M, dist q b' + dist q f = dist b' f →
      (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
        + dist r q + dist d b - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, b]
        + dist q f - workFnU C₀ σ ![r, p, f] ≤ lazyPot C₀ σ r)
    ∧ (∀ p q b b' d : M,
      (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
        + dist r q + dist d b - workFnU C₀ σ ![r, q, d] - workFnU C₀ σ ![r, q, b]
        + dist q b' - workFnU C₀ σ ![r, p, b'] ≤ lazyPot C₀ σ r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Case 1
    intro p q b b' d' f
    have hq := workFnU_quasiconvex_three M C₀ σ r b b' q f
    have s1 : workFnU C₀ σ ![r, b', f] = workFnU C₀ σ ![r, f, b'] := swap12 C₀ σ r b' f
    have s2 : workFnU C₀ σ ![r, b, f] = workFnU C₀ σ ![r, f, b] := swap12 C₀ σ r b f
    have s3 : workFnU C₀ σ ![r, b, b'] = workFnU C₀ σ ![r, b', b] := swap12 C₀ σ r b b'
    rcases min_cases (workFnU C₀ σ ![r, b, q] + workFnU C₀ σ ![r, b', f])
        (workFnU C₀ σ ![r, b, f] + workFnU C₀ σ ![r, b', q]) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] at hq
    · exact gaux1 C₀ σ r p q b b' d' f (by linarith)
    · have := gaux1 C₀ σ r p q b' b d' f (by linarith)
      linarith
  · intro p q b b' d d' f hp hr
    exact gaux2 C₀ σ r p q b b' d d' f hp hr
  · intro p X q b d d' f hcol
    exact gaux3red C₀ σ r p X q b d d' f hcol
  · intro p q b d d'
    exact gaux31 C₀ σ r p q b d d'
  · -- Case 3.2
    intro p q b d d' hcol
    have hq := workFnU_quasiconvex_three M C₀ σ r p b q d
    rcases min_cases (workFnU C₀ σ ![r, p, q] + workFnU C₀ σ ![r, b, d])
        (workFnU C₀ σ ![r, p, d] + workFnU C₀ σ ![r, b, q]) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] at hq
    · exact gaux32b C₀ σ r p q b d d' hcol hq
    · exact gaux32a C₀ σ r p q b d d' hcol hq
  · intro p q b f
    exact gaux331 C₀ σ r p q b f
  · intro p q b b' d f hcol
    exact gaux41 C₀ σ r p q b b' d f hcol
  · -- Case 4.2
    intro p q b b' d
    have hq := workFnU_quasiconvex_three M C₀ σ r q d p b'
    rcases min_cases (workFnU C₀ σ ![r, q, p] + workFnU C₀ σ ![r, d, b'])
        (workFnU C₀ σ ![r, q, b'] + workFnU C₀ σ ![r, d, p]) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] at hq
    · exact gaux42b C₀ σ r p q b b' d hq
    · exact gaux42 C₀ σ r p q b b' d hq
