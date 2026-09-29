-- Prove2me | solution 1 for KServer.workFnU_growth_two_server_inj
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T10:15:10.841954+00:00
-- url     : https://prove2.me/submissions/f99797b0-a9e5-42ce-bae6-6190548a298d

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_quasiconvex
import Theorems.Thm_KServer_workFn_rec_le
import Theorems.Thm_KServer_workFn_rec_ge
import Theorems.Thm_KServer_workFn_covered
import Theorems.Thm_KServer_workFn_mono
import Theorems.Thm_KServer_workFn_approx_offlineCost

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


/-! ### Auxiliary lemmas shared with the general construction -/

private theorem exists_min_approx (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Config k M, ∀ X : Config k M,
      workFnU C₀ σ A - ∑ i, dist r (A i) ≤ workFnU C₀ σ X - ∑ i, dist r (X i) + ε := by
  classical
  set g : Config k M → ℝ := fun V => workFnU C₀ σ V - ∑ i, dist r (V i) with hg
  have hbdd : BddBelow (Set.range g) := by
    refine ⟨-(∑ i, dist r (C₀ i)), ?_⟩
    rintro y ⟨V, rfl⟩
    have h := wfU_lower k hk M C₀ σ r V
    rw [hg]; simp only []; linarith
  have hne : (Set.range g).Nonempty := ⟨g C₀, ⟨C₀, rfl⟩⟩
  have hlt : sInf (Set.range g) < sInf (Set.range g) + ε := by linarith
  obtain ⟨y, hy, hylt⟩ := exists_lt_of_csInf_lt hne hlt
  obtain ⟨A, rfl⟩ := hy
  refine ⟨A, fun X => ?_⟩
  have h := csInf_le hbdd (Set.mem_range_self (f := g) X)
  have : g A ≤ g X + ε := by linarith
  rw [hg] at this
  simpa using this

private theorem take_succ_eq {M : Type} (σ : List M) (t : ℕ) (ht : t < σ.length) :
    σ.take (t + 1) = σ.take t ++ [σ[t]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht]
  rfl

private theorem geom_half_le_one (n : ℕ) :
    (∑ t ∈ Finset.range n, (1:ℝ) / 2 ^ (t + 1)) ≤ 1 := by
  have key : ∀ m : ℕ, (∑ t ∈ Finset.range m, (1:ℝ) / 2 ^ (t + 1)) = 1 - 1 / 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; field_simp; ring
  rw [key]
  have h1 : (0:ℝ) ≤ 1 / 2 ^ n := by positivity
  linarith

/-! ### Two-point configurations -/

/-- The configuration with first server at `x` and second server at `y`. -/
private def pr {M : Type} (x y : M) : Config 2 M := fun i => if i = 0 then x else y

private theorem pr0 {M : Type} (x y : M) : pr x y 0 = x := by simp [pr]

private theorem pr1 {M : Type} (x y : M) : pr x y 1 = y := by
  show (if (1 : Fin 2) = 0 then x else y) = y
  rw [if_neg (by decide)]

private theorem cfg_ext {M : Type} (X Y : Config 2 M) (h0 : X 0 = Y 0) (h1 : X 1 = Y 1) :
    X = Y := by
  funext i
  match i with
  | 0 => exact h0
  | 1 => exact h1

private theorem pr_eta {M : Type} (X : Config 2 M) : pr (X 0) (X 1) = X :=
  cfg_ext _ _ (pr0 _ _) (pr1 _ _)

private theorem pr_upd0 {M : Type} (x y r : M) : Function.update (pr x y) 0 r = pr r y := by
  refine cfg_ext _ _ ?_ ?_
  · rw [Function.update_self, pr0]
  · rw [Function.update_of_ne (by decide), pr1, pr1]

private theorem pr_upd1 {M : Type} (x y r : M) : Function.update (pr x y) 1 r = pr x r := by
  refine cfg_ext _ _ ?_ ?_
  · rw [Function.update_of_ne (by decide), pr0, pr0]
  · rw [Function.update_self, pr1]

private theorem pr_comp_swap {M : Type} (x y : M) :
    pr y x = (pr x y) ∘ (Equiv.swap (0 : Fin 2) 1) := by
  refine cfg_ext _ _ ?_ ?_
  · show pr y x 0 = pr x y (Equiv.swap (0 : Fin 2) 1 0)
    rw [Equiv.swap_apply_left, pr0, pr1]
  · show pr y x 1 = pr x y (Equiv.swap (0 : Fin 2) 1 1)
    rw [Equiv.swap_apply_right, pr1, pr0]

/-- The unordered work function does not see the order of the two servers. -/
private theorem wfU_pr_swap {M : Type} [MetricSpace M] (C₀ : Config 2 M) (σ : List M)
    (x y : M) : workFnU C₀ σ (pr y x) = workFnU C₀ σ (pr x y) := by
  rw [pr_comp_swap]
  exact workFnU_perm 2 M C₀ σ (pr x y) (Equiv.swap 0 1)

private theorem sum_pr {M : Type} [MetricSpace M] (v x y : M) :
    ∑ j, dist v (pr x y j) = dist v x + dist v y := by
  have h : ∑ j, dist v (pr x y j) = dist v (pr x y 0) + dist v (pr x y 1) :=
    Fin.sum_univ_two _
  rw [h, pr0, pr1]

/-- One step of the recurrence for a two-point configuration: the request is served by
one of the two servers. -/
private theorem step2 {M : Type} [MetricSpace M] (C₀ : Config 2 M) (σ : List M)
    (r x y : M) :
    workFnU C₀ (σ ++ [r]) (pr x y) = workFnU C₀ (σ ++ [r]) (pr r y) + dist r x
      ∨ workFnU C₀ (σ ++ [r]) (pr x y) = workFnU C₀ (σ ++ [r]) (pr x r) + dist r y := by
  obtain ⟨i, hi⟩ := wfU_step_self 2 (by norm_num) M C₀ σ r (pr x y)
  have hcase : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  rcases hcase i with h | h
  · subst h
    left
    rw [pr_upd0, pr0] at hi
    exact hi
  · subst h
    right
    rw [pr_upd1, pr1] at hi
    exact hi

/-! ### The two-server potential -/

/-- The `λ = 3` potential for two servers: one work-function value at a configuration
`A`, discounted by the distances from a shared point `b₀`, plus two work-function values
at configurations sharing the server `b₀`, discounted by the distance between their
second servers. -/
private noncomputable def Phi2 {M : Type} [MetricSpace M]
    (C₀ : Config 2 M) (σ : List M) (A : Config 2 M) (b₀ b₁ b₂ : M) : ℝ :=
  workFnU C₀ σ A - dist b₀ (A 0) - dist b₀ (A 1)
    + workFnU C₀ σ (pr b₀ b₁) + workFnU C₀ σ (pr b₀ b₂) - dist b₁ b₂

private noncomputable def Pot2 {M : Type} [MetricSpace M]
    (C₀ : Config 2 M) (σ : List M) : ℝ :=
  sInf (Set.range fun p : Config 2 M × M × M × M => Phi2 C₀ σ p.1 p.2.1 p.2.2.1 p.2.2.2)

private theorem Phi2_pr {M : Type} [MetricSpace M] (C₀ : Config 2 M) (σ : List M)
    (x y b₀ b₁ b₂ : M) :
    Phi2 C₀ σ (pr x y) b₀ b₁ b₂
      = workFnU C₀ σ (pr x y) - dist b₀ x - dist b₀ y
        + workFnU C₀ σ (pr b₀ b₁) + workFnU C₀ σ (pr b₀ b₂) - dist b₁ b₂ := by
  rw [Phi2, pr0, pr1]

private theorem Phi2_swapA {M : Type} [MetricSpace M] (C₀ : Config 2 M) (σ : List M)
    (x y b₀ b₁ b₂ : M) :
    Phi2 C₀ σ (pr y x) b₀ b₁ b₂ = Phi2 C₀ σ (pr x y) b₀ b₁ b₂ := by
  rw [Phi2_pr, Phi2_pr, wfU_pr_swap C₀ σ x y]
  ring

/-- The potential is bounded below by a constant depending only on `C₀`. -/
private theorem Phi2_lower {M : Type} [MetricSpace M] (C₀ : Config 2 M) (σ : List M)
    (A : Config 2 M) (b₀ b₁ b₂ : M) :
    -(3 * ∑ j, dist (C₀ 0) (C₀ j)) ≤ Phi2 C₀ σ A b₀ b₁ b₂ := by
  set v : M := C₀ 0 with hv
  have hA := wfU_lower 2 (by norm_num) M C₀ σ v A
  have hB1 := wfU_lower 2 (by norm_num) M C₀ σ v (pr b₀ b₁)
  have hB2 := wfU_lower 2 (by norm_num) M C₀ σ v (pr b₀ b₂)
  rw [sum_pr] at hB1 hB2
  have hAsum : ∑ i, dist v (A i) = dist v (A 0) + dist v (A 1) := Fin.sum_univ_two _
  rw [hAsum] at hA
  have t1 : dist b₀ (A 0) ≤ dist b₀ v + dist v (A 0) := dist_triangle _ _ _
  have t2 : dist b₀ (A 1) ≤ dist b₀ v + dist v (A 1) := dist_triangle _ _ _
  have t3 : dist b₁ b₂ ≤ dist b₁ v + dist v b₂ := dist_triangle _ _ _
  have e1 : dist b₀ v = dist v b₀ := dist_comm _ _
  have e2 : dist b₁ v = dist v b₁ := dist_comm _ _
  rw [Phi2]
  linarith

private theorem Pot2_le {M : Type} [MetricSpace M] (C₀ : Config 2 M) (σ : List M)
    (A : Config 2 M) (b₀ b₁ b₂ : M) : Pot2 C₀ σ ≤ Phi2 C₀ σ A b₀ b₁ b₂ := by
  refine csInf_le ⟨-(3 * ∑ j, dist (C₀ 0) (C₀ j)), ?_⟩ ⟨(A, b₀, b₁, b₂), rfl⟩
  rintro z ⟨p, rfl⟩
  exact Phi2_lower C₀ σ p.1 p.2.1 p.2.2.1 p.2.2.2

private theorem Pot2_ge {M : Type} [MetricSpace M] (C₀ : Config 2 M) (σ : List M) :
    -(3 * ∑ j, dist (C₀ 0) (C₀ j)) ≤ Pot2 C₀ σ := by
  refine le_csInf ⟨_, ⟨(C₀, C₀ 0, C₀ 0, C₀ 0), rfl⟩⟩ ?_
  rintro z ⟨p, rfl⟩
  exact Phi2_lower C₀ σ p.1 p.2.1 p.2.2.1 p.2.2.2

private theorem Pot2_approx {M : Type} [MetricSpace M] (C₀ : Config 2 M) (σ : List M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (A : Config 2 M) (b₀ b₁ b₂ : M), Phi2 C₀ σ A b₀ b₁ b₂ ≤ Pot2 C₀ σ + ε := by
  have hne : (Set.range fun p : Config 2 M × M × M × M =>
      Phi2 C₀ σ p.1 p.2.1 p.2.2.1 p.2.2.2).Nonempty :=
    ⟨_, ⟨(C₀, C₀ 0, C₀ 0, C₀ 0), rfl⟩⟩
  have hlt : Pot2 C₀ σ < Pot2 C₀ σ + ε := by linarith
  obtain ⟨z, hz, hzlt⟩ := exists_lt_of_csInf_lt hne hlt
  obtain ⟨p, rfl⟩ := hz
  exact ⟨p.1, p.2.1, p.2.2.1, p.2.2.2, le_of_lt hzlt⟩

/-! ### The shift lemma: the shared server may be placed at the last request -/

private theorem Phi2_shift_aux {M : Type} [MetricSpace M] (C₀ : Config 2 M) (σ : List M)
    (r a₁ a₂ b₀ b₁ b₂ : M)
    (hA : workFnU C₀ (σ ++ [r]) (pr a₁ a₂)
        = workFnU C₀ (σ ++ [r]) (pr a₁ r) + dist r a₂) :
    ∃ (A' : Config 2 M) (c₁ c₂ : M),
      Phi2 C₀ (σ ++ [r]) A' r c₁ c₂ ≤ Phi2 C₀ (σ ++ [r]) (pr a₁ a₂) b₀ b₁ b₂ := by
  have t1 : dist b₀ a₂ ≤ dist b₀ r + dist r a₂ := dist_triangle _ _ _
  have t2 : dist b₀ a₁ ≤ dist b₀ r + dist r a₁ := dist_triangle _ _ _
  have t3 : dist b₁ b₂ ≤ dist b₁ r + dist r b₂ := dist_triangle _ _ _
  have e0 : dist b₀ r = dist r b₀ := dist_comm _ _
  have e1 : dist b₁ r = dist r b₁ := dist_comm _ _
  have e2 : dist a₁ b₀ = dist b₀ a₁ := dist_comm _ _
  have hrr : dist r r = 0 := dist_self r
  rcases step2 C₀ σ r b₀ b₁ with h1 | h1 <;> rcases step2 C₀ σ r b₀ b₂ with h2 | h2
  · refine ⟨pr a₁ r, b₁, b₂, ?_⟩
    rw [Phi2_pr, Phi2_pr, h1, h2, hA]
    linarith
  · refine ⟨pr r b₁, a₁, b₀, ?_⟩
    rw [Phi2_pr, Phi2_pr, h1, h2, hA, wfU_pr_swap C₀ (σ ++ [r]) a₁ r,
      wfU_pr_swap C₀ (σ ++ [r]) b₀ r]
    linarith
  · refine ⟨pr r b₂, a₁, b₀, ?_⟩
    rw [Phi2_pr, Phi2_pr, h1, h2, hA, wfU_pr_swap C₀ (σ ++ [r]) a₁ r,
      wfU_pr_swap C₀ (σ ++ [r]) b₀ r]
    linarith
  · refine ⟨pr b₀ r, a₁, b₀, ?_⟩
    rw [Phi2_pr, Phi2_pr, h1, h2, hA, wfU_pr_swap C₀ (σ ++ [r]) a₁ r,
      wfU_pr_swap C₀ (σ ++ [r]) b₀ r]
    linarith

private theorem Phi2_shift_pr {M : Type} [MetricSpace M] (C₀ : Config 2 M) (σ : List M)
    (r x y b₀ b₁ b₂ : M) :
    ∃ (A' : Config 2 M) (c₁ c₂ : M),
      Phi2 C₀ (σ ++ [r]) A' r c₁ c₂ ≤ Phi2 C₀ (σ ++ [r]) (pr x y) b₀ b₁ b₂ := by
  rcases step2 C₀ σ r x y with h | h
  · have hA : workFnU C₀ (σ ++ [r]) (pr y x)
        = workFnU C₀ (σ ++ [r]) (pr y r) + dist r x := by
      rw [wfU_pr_swap C₀ (σ ++ [r]) x y, h, wfU_pr_swap C₀ (σ ++ [r]) r y]
    obtain ⟨A', c₁, c₂, hle⟩ := Phi2_shift_aux C₀ σ r y x b₀ b₁ b₂ hA
    exact ⟨A', c₁, c₂, by rw [← Phi2_swapA C₀ (σ ++ [r]) x y b₀ b₁ b₂]; exact hle⟩
  · exact Phi2_shift_aux C₀ σ r x y b₀ b₁ b₂ h

/-- **Lemma (shift).** In the minimisation defining the potential, the shared server may
be assumed to sit on the last request. -/
private theorem Phi2_shift {M : Type} [MetricSpace M] (C₀ : Config 2 M) (σ : List M)
    (r : M) (A : Config 2 M) (b₀ b₁ b₂ : M) :
    ∃ (A' : Config 2 M) (c₁ c₂ : M),
      Phi2 C₀ (σ ++ [r]) A' r c₁ c₂ ≤ Phi2 C₀ (σ ++ [r]) A b₀ b₁ b₂ := by
  have h := Phi2_shift_pr C₀ σ r (A 0) (A 1) b₀ b₁ b₂
  rw [pr_eta] at h
  exact h

/-! ### The potential is at most three times the offline optimum -/

private theorem Pot2_le_opt {M : Type} [MetricSpace M] (C₀ : Config 2 M) (σ : List M) :
    Pot2 C₀ σ ≤ 3 * offlineCost C₀ σ := by
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨X, hX⟩ := workFn_approx_offlineCost 2 (by norm_num) M C₀ σ (ε / 3) (by positivity)
  have hwf := wfU_self C₀ σ X
  have hle := Pot2_le C₀ σ X (X 0) (X 1) (X 1)
  have hval : Phi2 C₀ σ X (X 0) (X 1) (X 1)
      = 3 * workFnU C₀ σ X - dist (X 0) (X 1) := by
    rw [Phi2, pr_eta, dist_self, dist_self]
    ring
  rw [hval] at hle
  have hd : (0:ℝ) ≤ dist (X 0) (X 1) := dist_nonneg
  linarith

/-! ### The step bound -/

private theorem step_bound2 {M : Type} [MetricSpace M] (C₀ : Config 2 M) (σ : List M)
    (r : M) (ε : ℝ) (hε : 0 < ε) (X : Config 2 M) :
    workFnU C₀ (σ ++ [r]) X - workFnU C₀ σ X
      ≤ Pot2 C₀ (σ ++ [r]) - Pot2 C₀ σ + 3 * ε := by
  classical
  obtain ⟨A, hA⟩ := exists_min_approx 2 (by norm_num) M C₀ σ r ε hε
  obtain ⟨hA', hAmax⟩ := wfU_duality_approx 2 (by norm_num) M C₀ σ r A ε hA
  obtain ⟨A₀, b₀, b₁, b₂, hUB⟩ := Pot2_approx C₀ (σ ++ [r]) ε hε
  obtain ⟨A', c₁, c₂, hshift⟩ := Phi2_shift C₀ σ r A₀ b₀ b₁ b₂
  have hsub : Phi2 C₀ (σ ++ [r]) A r c₁ c₂ ≤ Phi2 C₀ (σ ++ [r]) A' r c₁ c₂ + ε := by
    have h := hA' A'
    have eA : ∑ i, dist r (A i) = dist r (A 0) + dist r (A 1) := Fin.sum_univ_two _
    have eA' : ∑ i, dist r (A' i) = dist r (A' 0) + dist r (A' 1) := Fin.sum_univ_two _
    rw [eA, eA'] at h
    rw [Phi2, Phi2]
    linarith
  have hchain : Phi2 C₀ (σ ++ [r]) A r c₁ c₂ ≤ Pot2 C₀ (σ ++ [r]) + 2 * ε := by linarith
  have hold := Pot2_le C₀ σ A r c₁ c₂
  have hmA : (0:ℝ) ≤ workFnU C₀ (σ ++ [r]) A - workFnU C₀ σ A := by
    have := wfU_mono 2 (by norm_num) M C₀ σ r A; linarith
  have hm1 : (0:ℝ) ≤ workFnU C₀ (σ ++ [r]) (pr r c₁) - workFnU C₀ σ (pr r c₁) := by
    have := wfU_mono 2 (by norm_num) M C₀ σ r (pr r c₁); linarith
  have hm2 : (0:ℝ) ≤ workFnU C₀ (σ ++ [r]) (pr r c₂) - workFnU C₀ σ (pr r c₂) := by
    have := wfU_mono 2 (by norm_num) M C₀ σ r (pr r c₂); linarith
  have hdiff : Phi2 C₀ (σ ++ [r]) A r c₁ c₂ - Phi2 C₀ σ A r c₁ c₂
      = (workFnU C₀ (σ ++ [r]) A - workFnU C₀ σ A)
        + (workFnU C₀ (σ ++ [r]) (pr r c₁) - workFnU C₀ σ (pr r c₁))
        + (workFnU C₀ (σ ++ [r]) (pr r c₂) - workFnU C₀ σ (pr r c₂)) := by
    rw [Phi2, Phi2]; ring
  have hAmaxX := hAmax X
  linarith

/-- **The total growth of the unordered work function for two servers is at most three
times the offline optimum**, up to an additive constant. -/
theorem solution (M : Type) [MetricSpace M] (C₀ : Config 2 M) :
    ∃ c : ℝ, ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config 2 M, Function.Injective X →
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ 3 * offlineCost C₀ σ + c := by
  classical
  refine ⟨3 * (∑ j, dist (C₀ 0) (C₀ j)) + 3, fun σ => ?_⟩
  refine ⟨fun t => (Pot2 C₀ (σ.take (t + 1)) - Pot2 C₀ (σ.take t))
      + 3 * ((1:ℝ) / 2 ^ (t + 1)), ?_, ?_⟩
  · intro t ht X _
    show workFnU C₀ (σ.take (t + 1)) X
      ≤ workFnU C₀ (σ.take t) X
        + ((Pot2 C₀ (σ.take (t + 1)) - Pot2 C₀ (σ.take t)) + 3 * ((1:ℝ) / 2 ^ (t + 1)))
    have hts : σ.take (t + 1) = σ.take t ++ [σ[t]] := take_succ_eq σ t ht
    have h := step_bound2 C₀ (σ.take t) σ[t] ((1:ℝ) / 2 ^ (t + 1)) (by positivity) X
    rw [← hts] at h
    linarith
  · show (∑ t ∈ Finset.range σ.length,
        ((Pot2 C₀ (σ.take (t + 1)) - Pot2 C₀ (σ.take t)) + 3 * ((1:ℝ) / 2 ^ (t + 1))))
      ≤ 3 * offlineCost C₀ σ + (3 * (∑ j, dist (C₀ 0) (C₀ j)) + 3)
    have hsplit : ∑ t ∈ Finset.range σ.length,
        ((Pot2 C₀ (σ.take (t + 1)) - Pot2 C₀ (σ.take t)) + 3 * ((1:ℝ) / 2 ^ (t + 1)))
        = (∑ t ∈ Finset.range σ.length, (Pot2 C₀ (σ.take (t + 1)) - Pot2 C₀ (σ.take t)))
          + 3 * ∑ t ∈ Finset.range σ.length, ((1:ℝ) / 2 ^ (t + 1)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have htel : ∑ t ∈ Finset.range σ.length,
        (Pot2 C₀ (σ.take (t + 1)) - Pot2 C₀ (σ.take t)) = Pot2 C₀ σ - Pot2 C₀ [] := by
      rw [Finset.sum_range_sub (fun t => Pot2 C₀ (σ.take t)) σ.length, List.take_length,
        List.take_zero]
    have hgeom := geom_half_le_one σ.length
    have hopt := Pot2_le_opt C₀ σ
    have hge := Pot2_ge C₀ ([] : List M)
    rw [hsplit, htel]
    linarith
