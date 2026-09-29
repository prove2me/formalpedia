-- Prove2me | solution 1 for KServer.lamPot_le_lazyPot_manhattan
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T18:34:06.276272+00:00
-- url     : https://prove2.me/submissions/27ca90ec-a3e4-41cf-aea9-2c796afe5c63

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential
import Theorems.Thm_KServer_shadow_eq_pinned
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_quasiconvex
import Theorems.Thm_KServer_workFn_rec_le
import Theorems.Thm_KServer_workFn_rec_ge
import Theorems.Thm_KServer_workFn_covered
import Theorems.Thm_KServer_workFn_mono
import Theorems.Thm_KServer_workFn_approx_offlineCost

import Theorems.Thm_KServer_workFnU_push
import Theorems.Thm_KServer_manhattan_bounding_rectangle
import Theorems.Thm_KServer_lamPot_instance_le_lazyPot_special
import Theorems.Thm_KServer_lamPot_instance_le_lazyPot_adjacent
import Theorems.Thm_KServer_lazyPot_ge_instance
import Theorems.Thm_KServer_lamPot_corner_dispatch

open KServer

private theorem wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem wfU_exists {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

private theorem wfU_self {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : workFnU C₀ σ X ≤ workFn C₀ σ X := by
  simpa using wfU_le C₀ σ X 1

private theorem mc_perm {k : ℕ} {M : Type} [MetricSpace M] (Y Z : Config k M)
    (π : Equiv.Perm (Fin k)) :
    moveCost (Y ∘ (π : Equiv.Perm (Fin k))) (Z ∘ (π : Equiv.Perm (Fin k))) = moveCost Y Z := by
  unfold moveCost
  exact Fintype.sum_equiv π (fun i => dist (Y (π i)) (Z (π i))) (fun j => dist (Y j) (Z j))
    (fun i => rfl)

private theorem sum_perm {k : ℕ} {M : Type} [MetricSpace M] (v : M) (Y : Config k M)
    (π : Equiv.Perm (Fin k)) : ∑ i, dist v (Y (π i)) = ∑ i, dist v (Y i) :=
  Fintype.sum_equiv π (fun i => dist v (Y (π i))) (fun i => dist v (Y i)) (fun i => rfl)

/-- The distance between the endpoints of a walk is at most its length. -/
private theorem dist_telescope {M : Type} [MetricSpace M] (f : ℕ → M) (n : ℕ) :
    dist (f 0) (f n) ≤ ∑ j ∈ Finset.range n, dist (f j) (f (j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have := dist_triangle (f 0) (f n) (f (n + 1))
      linarith

/-- The work function grows at unit rate away from the initial configuration: measured from
any base point, the target's total distance is paid for. -/
private theorem wfU_lower (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (v : M) (X : Config k M) :
    (∑ i, dist v (X i)) - (∑ i, dist v (C₀ i)) ≤ workFnU C₀ σ X := by
  classical
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ X
  rw [← hπ, ← sum_perm v X π]
  set Y : Config k M := X ∘ (π : Equiv.Perm (Fin k)) with hY
  show (∑ i, dist v (Y i)) - (∑ i, dist v (C₀ i)) ≤ workFn C₀ σ Y
  have hbdd : BddBelow {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
      c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
          + moveCost (S σ.length) Y} := by
    refine ⟨0, ?_⟩
    rintro c ⟨S, -, rfl⟩
    have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => dist_nonneg
    have h2 : (0:ℝ) ≤ moveCost (S σ.length) Y := Finset.sum_nonneg fun i _ => dist_nonneg
    linarith
  have hne : {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
      c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
          + moveCost (S σ.length) Y}.Nonempty := by
    have hk0 : (0 : ℕ) < k := hk
    refine ⟨_, ⟨fun j => if j = 0 then C₀ else fun _ => σ.getD (j - 1) (C₀ ⟨0, hk0⟩),
      ⟨by simp, ?_⟩, rfl⟩⟩
    intro j
    refine ⟨⟨0, hk0⟩, ?_⟩
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [List.getD_eq_getElem σ _ j.2]
    simp
  refine le_csInf hne ?_
  rintro c ⟨S, hS, rfl⟩
  have hcost : ∑ i, dist (C₀ i) (S σ.length i)
      ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) := by
    have hswap : ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))
        = ∑ i, ∑ j ∈ Finset.range σ.length, dist (S j i) (S (j + 1) i) := by
      unfold moveCost
      exact Finset.sum_comm
    rw [hswap]
    refine Finset.sum_le_sum fun i _ => ?_
    have := dist_telescope (fun j => S j i) σ.length
    rw [hS.1] at this
    exact this
  have hfin : ∑ i, dist (C₀ i) (Y i)
      ≤ (∑ i, dist (C₀ i) (S σ.length i)) + moveCost (S σ.length) Y := by
    unfold moveCost
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _
  have hbase : (∑ i, dist v (Y i)) - (∑ i, dist v (C₀ i)) ≤ ∑ i, dist (C₀ i) (Y i) := by
    have : ∀ i : Fin k, dist v (Y i) - dist v (C₀ i) ≤ dist (C₀ i) (Y i) := by
      intro i
      have := dist_triangle v (C₀ i) (Y i)
      linarith
    calc (∑ i, dist v (Y i)) - (∑ i, dist v (C₀ i))
        = ∑ i, (dist v (Y i) - dist v (C₀ i)) := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i, dist (C₀ i) (Y i) := Finset.sum_le_sum fun i _ => this i
  linarith

private theorem update_comp {k : ℕ} {M : Type} (X : Config k M) (i : Fin k) (r : M)
    (π : Equiv.Perm (Fin k)) :
    (Function.update X i r) ∘ (π : Equiv.Perm (Fin k))
      = Function.update (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i) r := by
  classical
  funext l
  by_cases h : l = π.symm i
  · subst h
    rw [Function.comp_apply, Equiv.apply_symm_apply, Function.update_self,
      Function.update_self]
  · have h2 : (π : Equiv.Perm (Fin k)) l ≠ i := by
      intro hc; exact h (by rw [← hc]; simp)
    simp [Function.update_of_ne h, Function.update_of_ne h2]

private theorem wfU_rec_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (i : Fin k) :
    workFnU C₀ (σ ++ [r]) X ≤ workFnU C₀ σ (Function.update X i r) + dist r (X i) := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ (Function.update X i r)
  have h1 := wfU_le C₀ (σ ++ [r]) X π
  have h2 := workFn_rec_le k hk M C₀ σ r (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i)
  rw [← update_comp X i r π] at h2
  have h3 : (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i) = X i := by simp
  rw [h3, hπ] at h2
  linarith

private theorem wfU_rec_ge (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    ∃ i : Fin k, workFnU C₀ σ (Function.update X i r) + dist r (X i)
      ≤ workFnU C₀ (σ ++ [r]) X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ (σ ++ [r]) X
  obtain ⟨i', hi'⟩ := workFn_rec_ge k hk M C₀ σ r (X ∘ (π : Equiv.Perm (Fin k)))
  refine ⟨π i', ?_⟩
  have hup : Function.update (X ∘ (π : Equiv.Perm (Fin k))) i' r
      = (Function.update X (π i') r) ∘ (π : Equiv.Perm (Fin k)) := by
    rw [update_comp X (π i') r π]; simp
  rw [hup] at hi'
  have h1 := wfU_le C₀ σ (Function.update X (π i') r) π
  have h2 : (X ∘ (π : Equiv.Perm (Fin k))) i' = X (π i') := rfl
  rw [h2, hπ] at hi'
  linarith

private theorem wfU_covered (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (hX : ∃ i, X i = r) :
    workFnU C₀ (σ ++ [r]) X = workFnU C₀ σ X := by
  unfold workFnU
  refine iInf_congr fun π => ?_
  refine workFn_covered k hk M C₀ σ r (X ∘ π) ?_
  obtain ⟨i, hi⟩ := hX
  exact ⟨π.symm i, by simpa using hi⟩

private theorem wfU_mono (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    workFnU C₀ σ X ≤ workFnU C₀ (σ ++ [r]) X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ (σ ++ [r]) X
  rw [← hπ]
  exact le_trans (wfU_le C₀ σ X π) (workFn_mono k hk M C₀ σ r (X ∘ π))

/-- One step of the recurrence, expressed purely in the new work function. -/
private theorem wfU_step_self (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (U : Config k M) :
    ∃ i : Fin k, workFnU C₀ (σ ++ [r]) U
      = workFnU C₀ (σ ++ [r]) (Function.update U i r) + dist r (U i) := by
  classical
  obtain ⟨i, hi⟩ := wfU_rec_ge k hk M C₀ σ r U
  refine ⟨i, le_antisymm ?_ ?_⟩
  · have hcov : ∃ l, (Function.update U i r) l = r := ⟨i, Function.update_self _ _ _⟩
    have hc := wfU_covered k hk M C₀ σ r (Function.update U i r) hcov
    have := wfU_rec_le k hk M C₀ σ r U i
    rw [← hc] at this
    exact this
  · have hcov : ∃ l, (Function.update U i r) l = r := ⟨i, Function.update_self _ _ _⟩
    have hc := wfU_covered k hk M C₀ σ r (Function.update U i r) hcov
    rw [hc]
    exact hi

private theorem sum_diff_single {k : ℕ} (F G : Fin k → ℝ) (p : Fin k)
    (h : ∀ i, i ≠ p → F i = G i) : ∑ i, F i - ∑ i, G i = F p - G p := by
  classical
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ p),
    ← Finset.add_sum_erase _ G (Finset.mem_univ p),
    Finset.sum_congr rfl (fun i hi => h i (Finset.ne_of_mem_erase hi))]
  ring

/-- The approximate duality property: an `ε`-minimiser of `w - d(r^k, ·)` is an
`ε`-minimiser for the new work function and an `ε`-maximiser of the increment. -/
private theorem wfU_duality_approx (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (A : Config k M) (ε : ℝ)
    (hA : ∀ X : Config k M, workFnU C₀ σ A - ∑ i, dist r (A i)
      ≤ workFnU C₀ σ X - ∑ i, dist r (X i) + ε) :
    (∀ X : Config k M, workFnU C₀ (σ ++ [r]) A - ∑ i, dist r (A i)
        ≤ workFnU C₀ (σ ++ [r]) X - ∑ i, dist r (X i) + ε) ∧
    (∀ X : Config k M, workFnU C₀ (σ ++ [r]) X - workFnU C₀ σ X
        ≤ workFnU C₀ (σ ++ [r]) A - workFnU C₀ σ A + ε) := by
  classical
  set D : Config k M → ℝ := fun V => ∑ i, dist r (V i) with hDdef
  set g : Config k M → ℝ := fun V => workFnU C₀ σ V - D V with hgdef
  have hgA : ∀ X : Config k M, g A ≤ g X + ε := hA
  have hDupd : ∀ (V : Config k M) (m : Fin k) (u : M),
      D (Function.update V m u) = D V - dist r (V m) + dist r u := by
    intro V m u
    have h := sum_diff_single (fun i => dist r (Function.update V m u i))
      (fun i => dist r (V i)) m (fun i hi => by
        show dist r (Function.update V m u i) = dist r (V i)
        rw [Function.update_of_ne hi])
    simp only [Function.update_self] at h
    rw [hDdef]
    linarith
  have hDperm : ∀ (V : Config k M) (π : Equiv.Perm (Fin k)),
      D (V ∘ (π : Equiv.Perm (Fin k))) = D V := by
    intro V π
    rw [hDdef]
    exact Fintype.sum_equiv π (fun i => dist r (V (π i))) (fun i => dist r (V i))
      (fun i => rfl)
  have hup : ∀ (V : Config k M) (l : Fin k),
      workFnU C₀ (σ ++ [r]) V - D V ≤ g (Function.update V l r) := by
    intro V l
    have h := wfU_rec_le k hk M C₀ σ r V l
    have hd := hDupd V l r
    rw [hgdef]; simp only []; rw [hd]
    simp only [dist_self, add_zero]
    linarith
  have hlow : ∀ V : Config k M, ∃ l : Fin k,
      g (Function.update V l r) ≤ workFnU C₀ (σ ++ [r]) V - D V := by
    intro V
    obtain ⟨l, hl⟩ := wfU_rec_ge k hk M C₀ σ r V
    refine ⟨l, ?_⟩
    have hd := hDupd V l r
    rw [hgdef]; simp only []; rw [hd]
    simp only [dist_self, add_zero]
    linarith
  have hkey : ∀ (P Q : Config k M) (m : Fin k), Q m = r →
      ∃ l : Fin k, g (Function.update P l r) + g A ≤ g Q + g P + ε := by
    intro P Q m hQm
    obtain ⟨π, hπ⟩ := workFnU_quasiconvex k hk M C₀ σ Q P
    refine ⟨π m, ?_⟩
    set s : Finset (Fin k) := Finset.univ.erase m with hsdef
    have hmem : ∀ l : Fin k, (l ∈ s) ↔ l ≠ m := by
      intro l; rw [hsdef]; simp [Finset.mem_erase]
    have hZ : (fun l => if l ∈ s then Q l else P (π l))
        = Function.update Q m (P (π m)) := by
      funext l
      show (if l ∈ s then Q l else P (π l)) = Function.update Q m (P (π m)) l
      by_cases hl : l = m
      · rw [hl, if_neg (by simp [hmem]), Function.update_self]
      · rw [if_pos ((hmem l).mpr hl), Function.update_of_ne hl]
    have hW : (fun l => if l ∈ s then P (π l) else Q l)
        = (Function.update P (π m) r) ∘ (π : Equiv.Perm (Fin k)) := by
      funext l
      show (if l ∈ s then P (π l) else Q l) = Function.update P (π m) r (π l)
      by_cases hl : l = m
      · rw [hl, if_neg (by simp [hmem]), Function.update_self, hQm]
      · have hne : (π : Equiv.Perm (Fin k)) l ≠ π m := fun hc => hl (π.injective hc)
        rw [if_pos ((hmem l).mpr hl), Function.update_of_ne hne]
    have hq := hπ s
    rw [hZ, hW, workFnU_perm k M C₀ σ (Function.update P (π m) r) π] at hq
    have hDZ := hDupd Q m (P (π m))
    have hDW := hDupd P (π m) r
    have hgZ := hgA (Function.update Q m (P (π m)))
    rw [hgdef] at hgZ ⊢
    simp only [] at hgZ ⊢
    rw [hDZ, hDW, hQm] at *
    simp only [dist_self, sub_zero, add_zero] at *
    linarith
  constructor
  · intro X
    obtain ⟨l₀, hl₀⟩ := hlow X
    obtain ⟨l, hl⟩ := hkey A (Function.update X l₀ r) l₀ (Function.update_self _ _ _)
    have h1 := hup A l
    simp only [hgdef, hDdef] at hl h1 hl₀
    linarith
  · intro X
    obtain ⟨m₀, hm₀⟩ := hlow A
    obtain ⟨l, hl⟩ := hkey X (Function.update A m₀ r) m₀ (Function.update_self _ _ _)
    have h1 := hup X l
    simp only [hgdef, hDdef] at hl h1 hm₀
    linarith


/-! ### Boundedness of the suprema -/

section Bnd
variable {M : Type} [MetricSpace M] (C₀ : Config 3 M) (σ : List M)

private theorem sum3' (x : M) (A : Config 3 M) :
    (∑ i, dist x (A i)) = dist x (A 0) + dist x (A 1) + dist x (A 2) :=
  Fin.sum_univ_three _

private theorem lower3 (x e e' : M) :
    dist x e + dist x e' - (∑ i, dist x (C₀ i)) ≤ workFnU C₀ σ ![x, e, e'] := by
  have h := wfU_lower 3 (by norm_num) M C₀ σ x ![x, e, e']
  rw [sum3'] at h
  have h0 : dist x ((![x, e, e'] : Config 3 M) 0) = 0 := dist_self x
  have e1 : (![x, e, e'] : Config 3 M) 1 = e := rfl
  have e2 : (![x, e, e'] : Config 3 M) 2 = e' := rfl
  rw [h0, e1, e2] at h
  linarith

private theorem bdd2 (x y : M) : BddAbove (Set.range fun q : M × M =>
    dist y q.1 + dist y q.2 - workFnU C₀ σ ![x, q.1, q.2]) := by
  refine ⟨2 * dist y x + ∑ i, dist x (C₀ i), ?_⟩
  rintro t ⟨⟨e, e'⟩, rfl⟩
  have h := lower3 C₀ σ x e e'
  have t1 : dist y e ≤ dist y x + dist x e := dist_triangle _ _ _
  have t2 : dist y e' ≤ dist y x + dist x e' := dist_triangle _ _ _
  simp only []
  linarith

private theorem shadow2_le (x y : M) :
    shadow₂ C₀ σ x y ≤ 2 * dist y x + ∑ i, dist x (C₀ i) := by
  refine csSup_le ⟨_, ⟨(x, x), rfl⟩⟩ ?_
  rintro t ⟨⟨e, e'⟩, rfl⟩
  have h := lower3 C₀ σ x e e'
  have t1 : dist y e ≤ dist y x + dist x e := dist_triangle _ _ _
  have t2 : dist y e' ≤ dist y x + dist x e' := dist_triangle _ _ _
  simp only []
  linarith

private theorem bddD (x : M) : BddAbove (Set.range fun t : M × M × M =>
    shadow₂ C₀ σ x t.1 + dist t.2.1 t.2.2
      - workFnU C₀ σ ![x, t.1, t.2.1] - workFnU C₀ σ ![x, t.1, t.2.2]) := by
  refine ⟨3 * ∑ i, dist x (C₀ i), ?_⟩
  rintro t ⟨⟨p, d, d'⟩, rfl⟩
  have hs := shadow2_le C₀ σ x p
  have h1 := lower3 C₀ σ x p d
  have h2 := lower3 C₀ σ x p d'
  have t1 : dist d d' ≤ dist d x + dist x d' := dist_triangle _ _ _
  have e1 : dist d x = dist x d := dist_comm _ _
  have e2 : dist p x = dist x p := dist_comm _ _
  simp only []
  linarith

end Bnd

/-- Extract an `ε`-witness from a supremum. -/
private theorem sup_witness {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddAbove S)
    (ε : ℝ) (hε : 0 < ε) : ∃ t ∈ S, sSup S ≤ t + ε := by
  obtain ⟨t, htS, ht⟩ := exists_lt_of_lt_csSup hne (show sSup S - ε < sSup S by linarith)
  exact ⟨t, htS, by linarith⟩

section Bnd2
variable {M : Type} [MetricSpace M] (C₀ : Config 3 M) (σ : List M)

private theorem bddLam (x : M) : BddAbove (Set.range fun t : M × M × M × M =>
    -dist x t.1 + shadow₂ C₀ σ x t.1 - dist x t.2.1 + shadow₂ C₀ σ x t.2.1
      - workFnU C₀ σ ![x, t.1, t.2.1]
      + dist t.2.2.1 t.2.2.2 - workFnU C₀ σ ![x, t.2.2.1, t.2.2.2]) := by
  refine ⟨4 * ∑ i, dist x (C₀ i), ?_⟩
  rintro t ⟨⟨p, q, e, e'⟩, rfl⟩
  have hp := shadow2_le C₀ σ x p
  have hq := shadow2_le C₀ σ x q
  have h1 := lower3 C₀ σ x p q
  have h2 := lower3 C₀ σ x e e'
  have t1 : dist e e' ≤ dist e x + dist x e' := dist_triangle _ _ _
  have ep : dist p x = dist x p := dist_comm _ _
  have eq' : dist q x = dist x q := dist_comm _ _
  have ee : dist e x = dist x e := dist_comm _ _
  simp only []
  linarith

private theorem bddGam (x : M) : BddAbove (Set.range fun t : M × M × M × M × M =>
    -dist x t.1 + shadow₂ C₀ σ x t.1 + dist x t.2.1
      + dist t.2.2.1 t.2.2.2.1
      - workFnU C₀ σ ![x, t.2.1, t.2.2.1] - workFnU C₀ σ ![x, t.2.1, t.2.2.2.1]
      + dist t.2.1 t.2.2.2.2 - workFnU C₀ σ ![x, t.1, t.2.2.2.2]) := by
  refine ⟨4 * ∑ i, dist x (C₀ i), ?_⟩
  rintro t ⟨⟨p, q, d, d', f⟩, rfl⟩
  have hp := shadow2_le C₀ σ x p
  have h1 := lower3 C₀ σ x q d
  have h2 := lower3 C₀ σ x q d'
  have h3 := lower3 C₀ σ x p f
  have t1 : dist d d' ≤ dist d x + dist x d' := dist_triangle _ _ _
  have t2 : dist q f ≤ dist q x + dist x f := dist_triangle _ _ _
  have ep : dist p x = dist x p := dist_comm _ _
  have ed : dist d x = dist x d := dist_comm _ _
  have eq' : dist q x = dist x q := dist_comm _ _
  simp only []
  linarith

end Bnd2

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

set_option maxHeartbeats 1000000 in
/-- **Lemma 5 of Bein, Chrobak and Larmore.** -/
theorem solution (C₀ : Config 3 (PiLp 1 fun _ : Fin 2 => ℝ))
    (σ : List (PiLp 1 fun _ : Fin 2 => ℝ)) (r : PiLp 1 fun _ : Fin 2 => ℝ) :
    lamPot C₀ σ r ≤ lazyPot C₀ σ r := by
  classical
  have key : ∀ p q b b' c c' e e' : PiLp 1 fun _ : Fin 2 => ℝ,
      LamI C₀ σ r p b b' q c c' e e' ≤ lazyPot C₀ σ r := by
    intro p q b b' c c' e e'
    obtain ⟨T, x, z, y, t, hST, hxT, hzT, hyT, htT, hd, hbox, hcor⟩ :=
      manhattan_bounding_rectangle ({p, q, b, b', c, c', e, e'} : Finset _)
    have hpT : p ∈ T := hST (by simp)
    have hqT : q ∈ T := hST (by simp)
    have hbT : b ∈ T := hST (by simp)
    have hb'T : b' ∈ T := hST (by simp)
    have hcT : c ∈ T := hST (by simp)
    have hc'T : c' ∈ T := hST (by simp)
    have heT : e ∈ T := hST (by simp)
    have he'T : e' ∈ T := hST (by simp)
    have hcorT : ∀ u : PiLp 1 fun _ : Fin 2 => ℝ,
        (u = x ∨ u = z ∨ u = y ∨ u = t) → u ∈ T := by
      rintro u (rfl | rfl | rfl | rfl) <;> assumption
    obtain ⟨u1, hu1c, hu1⟩ := hcor p hpT b hbT
    obtain ⟨u2, hu2c, hu2⟩ := hcor p hpT b' hb'T
    have sB1 := workFnU_push _ C₀ σ r p b b' u1 hu1
    have sB2 := workFnU_push _ C₀ σ r p b' u1 u2 hu2
    have swB1 : workFnU C₀ σ ![r, u1, b'] = workFnU C₀ σ ![r, b', u1] := swap12 C₀ σ r u1 b'
    have swB2 : workFnU C₀ σ ![r, u2, u1] = workFnU C₀ σ ![r, u1, u2] := swap12 C₀ σ r u2 u1
    have hBred : dist p b + dist p b' - workFnU C₀ σ ![r, b, b']
        ≤ dist p u1 + dist p u2 - workFnU C₀ σ ![r, u1, u2] := by linarith
    obtain ⟨v1, hv1c, hv1⟩ := hcor q hqT c hcT
    obtain ⟨v2, hv2c, hv2⟩ := hcor q hqT c' hc'T
    have sC1 := workFnU_push _ C₀ σ r q c c' v1 hv1
    have sC2 := workFnU_push _ C₀ σ r q c' v1 v2 hv2
    have swC1 : workFnU C₀ σ ![r, v1, c'] = workFnU C₀ σ ![r, c', v1] := swap12 C₀ σ r v1 c'
    have swC2 : workFnU C₀ σ ![r, v2, v1] = workFnU C₀ σ ![r, v1, v2] := swap12 C₀ σ r v2 v1
    have hCred : dist q c + dist q c' - workFnU C₀ σ ![r, c, c']
        ≤ dist q v1 + dist q v2 - workFnU C₀ σ ![r, v1, v2] := by linarith
    obtain ⟨w1, hw1c, hw1⟩ := hcor e' he'T e heT
    have hw1T : w1 ∈ T := hcorT w1 hw1c
    obtain ⟨w2, hw2c, hw2⟩ := hcor w1 hw1T e' he'T
    have hw2T : w2 ∈ T := hcorT w2 hw2c
    have sE1 := workFnU_push _ C₀ σ r e' e e' w1 hw1
    have sE2 := workFnU_push _ C₀ σ r w1 e' w1 w2 hw2
    have dse : dist e' e' = 0 := dist_self e'
    have dsw : dist w1 w1 = 0 := dist_self w1
    have dce : dist e' e = dist e e' := dist_comm e' e
    have swE1 : workFnU C₀ σ ![r, w1, e'] = workFnU C₀ σ ![r, e', w1] := swap12 C₀ σ r w1 e'
    have dcw : dist e' w1 = dist w1 e' := dist_comm e' w1
    have hEred : dist e e' - workFnU C₀ σ ![r, e, e']
        ≤ dist w1 w2 - workFnU C₀ σ ![r, w2, w1] := by linarith
    have hfinal : ∃ E E' : PiLp 1 fun _ : Fin 2 => ℝ,
        ((E = x ∧ E' = y) ∨ (E = z ∧ E' = t) ∨ (E = y ∧ E' = x) ∨ (E = t ∧ E' = z))
        ∧ dist w1 w2 - workFnU C₀ σ ![r, w2, w1]
            ≤ dist E E' - workFnU C₀ σ ![r, E, E'] := by
      have hb2 := hbox w2 hw2T
      rcases hw1c with hh | hh | hh | hh
      · refine ⟨x, y, Or.inl ⟨rfl, rfl⟩, ?_⟩
        rw [hh]
        have s := workFnU_push _ C₀ σ r x w2 x y hb2.1
        have sw : workFnU C₀ σ ![r, y, x] = workFnU C₀ σ ![r, x, y] := swap12 C₀ σ r y x
        have d0 : dist x x = 0 := dist_self x
        linarith
      · refine ⟨z, t, Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
        rw [hh]
        have s := workFnU_push _ C₀ σ r z w2 z t hb2.2
        have sw : workFnU C₀ σ ![r, t, z] = workFnU C₀ σ ![r, z, t] := swap12 C₀ σ r t z
        have d0 : dist z z = 0 := dist_self z
        linarith
      · refine ⟨y, x, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_⟩
        rw [hh]
        have hyx : dist y w2 + dist w2 x = dist y x := by
          have h := hb2.1
          rw [dist_comm y w2, dist_comm w2 x, dist_comm y x]; linarith
        have s := workFnU_push _ C₀ σ r y w2 y x hyx
        have sw : workFnU C₀ σ ![r, x, y] = workFnU C₀ σ ![r, y, x] := swap12 C₀ σ r x y
        have d0 : dist y y = 0 := dist_self y
        linarith
      · refine ⟨t, z, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), ?_⟩
        rw [hh]
        have htz : dist t w2 + dist w2 z = dist t z := by
          have h := hb2.2
          rw [dist_comm t w2, dist_comm w2 z, dist_comm t z]; linarith
        have s := workFnU_push _ C₀ σ r t w2 t z htz
        have sw : workFnU C₀ σ ![r, z, t] = workFnU C₀ σ ![r, t, z] := swap12 C₀ σ r z t
        have d0 : dist t t = 0 := dist_self t
        linarith
    obtain ⟨E, E', hEE, hEfin⟩ := hfinal
    have hle : LamI C₀ σ r p b b' q c c' e e'
        ≤ LamI C₀ σ r p u1 u2 q v1 v2 E E' := by
      unfold LamI; linarith
    refine le_trans hle ?_
    exact lamPot_corner_dispatch _ C₀ σ r x z y t p q (hbox p hpT).1 (hbox p hpT).2
      (hbox q hqT).1 (hbox q hqT).2 u1 u2 v1 v2 E E' hu1c hu2c hv1c hv2c hEE
  -- from the pointwise bound to the potential
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨s1, ⟨⟨p, q, e, e'⟩, rfl⟩, h1⟩ := sup_witness
    (⟨_, ⟨(r, r, r, r), rfl⟩⟩ : (Set.range fun w : _ × _ × _ × _ =>
      -dist r w.1 + shadow₂ C₀ σ r w.1 - dist r w.2.1 + shadow₂ C₀ σ r w.2.1
        - workFnU C₀ σ ![r, w.1, w.2.1]
        + dist w.2.2.1 w.2.2.2 - workFnU C₀ σ ![r, w.2.2.1, w.2.2.2]).Nonempty)
    (bddLam C₀ σ r) (ε / 3) (by positivity)
  obtain ⟨s2, ⟨⟨b, b'⟩, rfl⟩, h2⟩ := sup_witness
    (⟨_, ⟨(r, r), rfl⟩⟩ : (Set.range fun w : _ × _ =>
      dist p w.1 + dist p w.2 - workFnU C₀ σ ![r, w.1, w.2]).Nonempty)
    (bdd2 C₀ σ r p) (ε / 3) (by positivity)
  obtain ⟨s3, ⟨⟨c, c'⟩, rfl⟩, h3⟩ := sup_witness
    (⟨_, ⟨(r, r), rfl⟩⟩ : (Set.range fun w : _ × _ =>
      dist q w.1 + dist q w.2 - workFnU C₀ σ ![r, w.1, w.2]).Nonempty)
    (bdd2 C₀ σ r q) (ε / 3) (by positivity)
  dsimp only at h1 h2 h3
  have h2' : shadow₂ C₀ σ r p
      ≤ dist p b + dist p b' - workFnU C₀ σ ![r, b, b'] + ε / 3 := by
    rw [shadow₂]; exact h2
  have h3' : shadow₂ C₀ σ r q
      ≤ dist q c + dist q c' - workFnU C₀ σ ![r, c, c'] + ε / 3 := by
    rw [shadow₂]; exact h3
  have hb := key p q b b' c c' e e'
  unfold LamI at hb
  rw [lamPot]
  linarith
