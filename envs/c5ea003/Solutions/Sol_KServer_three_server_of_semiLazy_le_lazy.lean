-- Prove2me | solution 1 for KServer.three_server_of_semiLazy_le_lazy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T17:17:02.698423+00:00
-- url     : https://prove2.me/submissions/530e5174-539f-4d02-b997-0fbcd85c9e41

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_quasiconvex
import Theorems.Thm_KServer_workFn_rec_le
import Theorems.Thm_KServer_workFn_rec_ge
import Theorems.Thm_KServer_workFn_covered
import Theorems.Thm_KServer_workFn_mono
import Theorems.Thm_KServer_workFn_approx_offlineCost
import Definitions.Def_KServer_lazy_potential
import Theorems.Thm_KServer_workFn_nil
import Theorems.Thm_KServer_lazyPot_offset
import Theorems.Thm_KServer_lazyPot_le_semiLazyPot
import Theorems.Thm_KServer_potential_criterion
import Theorems.Thm_KServer_shadow_update

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


section Init
variable {k : ℕ} {M : Type} [MetricSpace M]

/-- Requesting a point already occupied in the initial configuration is free. -/
private theorem wfU_init (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (j : Fin k) (X : Config k M) :
    workFnU C₀ ([] ++ [C₀ j]) X = workFnU C₀ [] X := by
  classical
  refine le_antisymm ?_ (wfU_mono k hk M C₀ [] (C₀ j) X)
  obtain ⟨π, hπ⟩ := wfU_exists C₀ ([] : List M) X
  have hstep := wfU_rec_le k hk M C₀ ([] : List M) (C₀ j) X (π j)
  have hle : workFnU C₀ ([] : List M) (Function.update X (π j) (C₀ j))
      ≤ workFn C₀ ([] : List M)
          ((Function.update X (π j) (C₀ j)) ∘ (π : Equiv.Perm (Fin k))) :=
    wfU_le C₀ [] (Function.update X (π j) (C₀ j)) π
  rw [workFn_nil k hk M C₀ _] at hle
  rw [workFn_nil k hk M C₀ _] at hπ
  have hsum := sum_diff_single
    (fun m => dist (C₀ m) ((Function.update X (π j) (C₀ j)) (π m)))
    (fun m => dist (C₀ m) (X (π m))) j
    (fun m hm => by
      have hne : π m ≠ π j := fun h => hm (π.injective h)
      show dist (C₀ m) ((Function.update X (π j) (C₀ j)) (π m)) = dist (C₀ m) (X (π m))
      rw [Function.update_of_ne hne])
  dsimp only at hsum
  rw [Function.update_self, dist_self] at hsum
  have hmc : moveCost C₀ ((Function.update X (π j) (C₀ j)) ∘ (π : Equiv.Perm (Fin k)))
      = ∑ m, dist (C₀ m) ((Function.update X (π j) (C₀ j)) (π m)) := rfl
  have hmc2 : moveCost C₀ (X ∘ (π : Equiv.Perm (Fin k)))
      = ∑ m, dist (C₀ m) (X (π m)) := rfl
  rw [hmc] at hle
  rw [hmc2] at hπ
  linarith

end Init

section Perm
variable {M : Type} [MetricSpace M]

private theorem cfg3_eta (A : Config 3 M) : ![A 0, A 1, A 2] = A := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

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

/-- A three-point configuration containing `r` is, up to relabelling, `![r, a, b]`. -/
private theorem pin3 (C₀ : Config 3 M) (σ : List M) (Y : Config 3 M) (i : Fin 3) (r : M)
    (hY : Y i = r) : ∃ a b : M, workFnU C₀ σ Y = workFnU C₀ σ ![r, a, b] := by
  match i with
  | 0 => exact ⟨Y 1, Y 2, by rw [← hY, cfg3_eta]⟩
  | 1 => refine ⟨Y 0, Y 2, ?_⟩
         rw [← hY, ← cfg3_eta Y, swap01 C₀ σ (Y 0) (Y 1) (Y 2)]
         rfl
  | 2 => refine ⟨Y 0, Y 1, ?_⟩
         rw [← hY, ← cfg3_eta Y, rot3 C₀ σ (Y 0) (Y 1) (Y 2)]
         rfl

end Perm

section T1
variable {M : Type} [MetricSpace M]

private theorem lazy_congr (C₀ : Config 3 M) (σ τ : List M)
    (hf : workFnU C₀ σ = workFnU C₀ τ) (x : M) :
    lazyPot C₀ σ x = lazyPot C₀ τ x := by
  simp only [lazyPot, shadow, dotW, shadow₂, hf]

private theorem cover3 (C₀ : Config 3 M) (τ : List M) (s u v : M) :
    workFnU C₀ (τ ++ [s]) ![s, u, v] = workFnU C₀ τ ![s, u, v] :=
  wfU_covered 3 (by norm_num) M C₀ τ s ![s, u, v] ⟨0, rfl⟩

private theorem dotW_stable (C₀ : Config 3 M) (τ : List M) (s : M) :
    dotW C₀ (τ ++ [s]) s = dotW C₀ τ s := by
  have h2 : ∀ y : M, shadow₂ C₀ (τ ++ [s]) s y = shadow₂ C₀ τ s y := by
    intro y; simp only [shadow₂, cover3]
  simp only [dotW, h2, cover3]

/-- The offset property. -/
private theorem op_aux (C₀ : Config 3 M) (σ : List M) (r : M) (X : Config 3 M) :
    0 ≤ lazyPot C₀ (σ ++ [r]) r + 4 * workFnU C₀ (σ ++ [r]) X := by
  classical
  obtain ⟨i, hi⟩ := wfU_step_self 3 (by norm_num) M C₀ σ r X
  have hYi : (Function.update X i r) i = r := Function.update_self _ _ _
  obtain ⟨a, b, hab⟩ := pin3 C₀ (σ ++ [r]) (Function.update X i r) i r hYi
  have hoff := lazyPot_offset M C₀ (σ ++ [r]) r a b
  have hd : (0:ℝ) ≤ dist r (X i) := dist_nonneg
  have h1 : (0:ℝ) ≤ dist r a := dist_nonneg
  have h2 : (0:ℝ) ≤ dist r b := dist_nonneg
  have h3 : (0:ℝ) ≤ dist a b := dist_nonneg
  rw [hab] at hi
  linarith

end T1

/-- **Theorem 1 of Bein, Chrobak and Larmore.** -/
theorem solution (M : Type) [MetricSpace M] (C₀ X₀ : Config 3 M)
    (hX₀ : Function.Injective X₀)
    (hspace : ∀ (σ : List M) (r : M),
      semiLazyPot C₀ (σ ++ [r]) r ≤ lazyPot C₀ (σ ++ [r]) r) :
    ∃ A : OnlineAlgorithm 3 M, A.conf [] = C₀ ∧ IsCompetitive A 3 := by
  classical
  have hk : 1 ≤ 3 := by norm_num
  have hfe : workFnU C₀ ([] : List M) = workFnU C₀ ([] ++ [C₀ 0]) := by
    funext X
    exact (wfU_init 3 hk M C₀ 0 X).symm
  have hnil : lazyPot C₀ ([] : List M) (C₀ 0) = lazyPot C₀ ([] ++ [C₀ 0]) (C₀ 0) :=
    lazy_congr C₀ [] ([] ++ [C₀ 0]) hfe (C₀ 0)
  refine potential_criterion 3 hk M C₀ X₀ hX₀ 3 (by norm_num)
    (fun τ => lazyPot C₀ τ ((τ.getLast?).getD (C₀ 0))) ?_ ?_
  · -- offset property
    intro τ X
    induction τ using List.reverseRecOn with
    | nil =>
        have h := op_aux C₀ [] (C₀ 0) X
        have hX : workFnU C₀ ([] : List M) X = workFnU C₀ ([] ++ [C₀ 0]) X := by rw [hfe]
        simp only [List.getLast?_nil, Option.getD_none]
        rw [hnil, hX]
        linarith
    | append_singleton τ' r _ =>
        have h := op_aux C₀ τ' r X
        simp only [List.getLast?_concat, Option.getD_some]
        linarith
  · -- update property
    intro τ s X _
    have hcor := (shadow_update 3 hk M C₀ τ s).1 X
    have hdot := dotW_stable C₀ τ s
    have hstep : lazyPot C₀ (τ ++ [s]) s + workFnU C₀ (τ ++ [s]) X
        ≤ lazyPot C₀ τ s + workFnU C₀ τ X := by
      rw [lazyPot, lazyPot, hdot]
      linarith
    have hlast : lazyPot C₀ τ s ≤ lazyPot C₀ τ ((τ.getLast?).getD (C₀ 0)) := by
      induction τ using List.reverseRecOn with
      | nil =>
          simp only [List.getLast?_nil, Option.getD_none]
          rw [hnil, lazy_congr C₀ [] ([] ++ [C₀ 0]) hfe s]
          exact le_trans (lazyPot_le_semiLazyPot M C₀ [] (C₀ 0) s) (hspace [] (C₀ 0))
      | append_singleton τ' r _ =>
          simp only [List.getLast?_concat, Option.getD_some]
          exact le_trans (lazyPot_le_semiLazyPot M C₀ τ' r s) (hspace τ' r)
    simp only [List.getLast?_concat, Option.getD_some]
    linarith
