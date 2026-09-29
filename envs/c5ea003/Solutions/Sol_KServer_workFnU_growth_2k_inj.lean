-- Prove2me | solution 1 for KServer.workFnU_growth_2k_inj
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T09:10:37.999171+00:00
-- url     : https://prove2.me/submissions/0adc4450-efa3-42d2-95c7-119450e30557

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

/-- The Koutsoupias--Papadimitriou expression: `k` copies of the work function at `U`
together with one at each `B i`, discounted by the distances from `U i` to `B i`. -/
private noncomputable def PsiV {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (U : Config k M) (B : Fin k → Config k M) : ℝ :=
  (k : ℝ) * workFnU C₀ σ U + ∑ i, (workFnU C₀ σ (B i) - ∑ j, dist (U i) (B i j))

private noncomputable def PotV {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : ℝ :=
  sInf (Set.range fun p : Config k M × (Fin k → Config k M) => PsiV C₀ σ p.1 p.2)

/-- The potential is bounded below by a constant depending only on the initial
configuration. -/
private theorem Psi_lower (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (U : Config k M) (B : Fin k → Config k M) :
    -(2 * (k : ℝ) * ∑ j, dist (C₀ ⟨0, hk⟩) (C₀ j)) ≤ PsiV C₀ σ U B := by
  classical
  set v : M := C₀ ⟨0, hk⟩ with hv
  set Kv : ℝ := ∑ j, dist v (C₀ j) with hKv
  have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hU : (∑ j, dist v (U j)) - Kv ≤ workFnU C₀ σ U := wfU_lower k hk M C₀ σ v U
  have hB : ∀ i : Fin k,
      -(∑ j, dist (U i) (C₀ j)) ≤ workFnU C₀ σ (B i) - ∑ j, dist (U i) (B i j) := by
    intro i
    have := wfU_lower k hk M C₀ σ (U i) (B i)
    linarith
  have hCB : ∀ i : Fin k, ∑ j, dist (U i) (C₀ j) ≤ (k : ℝ) * dist (U i) v + Kv := by
    intro i
    have h1 : ∀ j : Fin k, dist (U i) (C₀ j) ≤ dist (U i) v + dist v (C₀ j) :=
      fun j => dist_triangle _ _ _
    calc ∑ j, dist (U i) (C₀ j) ≤ ∑ j : Fin k, (dist (U i) v + dist v (C₀ j)) :=
          Finset.sum_le_sum fun j _ => h1 j
      _ = (k : ℝ) * dist (U i) v + Kv := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            hKv]
          simp [mul_comm]
  have hsum : ∑ i, (workFnU C₀ σ (B i) - ∑ j, dist (U i) (B i j))
      ≥ ∑ i : Fin k, (-((k : ℝ) * dist (U i) v + Kv)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := hB i
    have := hCB i
    linarith
  have hcollapse : ∑ i : Fin k, (-((k : ℝ) * dist (U i) v + Kv))
      = -((k : ℝ) * ∑ i, dist (U i) v) - (k : ℝ) * Kv := by
    have e1 : ∑ i : Fin k, ((k : ℝ) * dist (U i) v + Kv)
        = (k : ℝ) * (∑ i, dist (U i) v) + (k : ℝ) * Kv := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have e2 : ∑ i : Fin k, (-((k : ℝ) * dist (U i) v + Kv))
        + ∑ i : Fin k, ((k : ℝ) * dist (U i) v + Kv) = 0 := by
      rw [← Finset.sum_add_distrib]
      simp
    linarith [e1, e2]
  have hsymm : ∑ j, dist v (U j) = ∑ i, dist (U i) v :=
    Finset.sum_congr rfl fun i _ => dist_comm _ _
  have hkU : (k : ℝ) * ((∑ j, dist v (U j)) - Kv) ≤ (k : ℝ) * workFnU C₀ σ U :=
    mul_le_mul_of_nonneg_left hU hk0
  rw [PsiV]
  rw [hcollapse] at hsum
  rw [hsymm, mul_sub] at hkU
  have h2 : (2:ℝ) * (k : ℝ) * Kv = (k : ℝ) * Kv + (k : ℝ) * Kv := by ring
  linarith [hkU, hsum, h2]

private theorem Pot_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (U : Config k M) (B : Fin k → Config k M) :
    PotV C₀ σ ≤ PsiV C₀ σ U B := by
  refine csInf_le ⟨-(2 * (k : ℝ) * ∑ j, dist (C₀ ⟨0, hk⟩) (C₀ j)), ?_⟩ ⟨(U, B), rfl⟩
  rintro y ⟨p, rfl⟩
  exact Psi_lower k hk M C₀ σ p.1 p.2

private theorem Pot_ge (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) :
    -(2 * (k : ℝ) * ∑ j, dist (C₀ ⟨0, hk⟩) (C₀ j)) ≤ PotV C₀ σ := by
  refine le_csInf ⟨_, ⟨(C₀, fun _ => C₀), rfl⟩⟩ ?_
  rintro y ⟨p, rfl⟩
  exact Psi_lower k hk M C₀ σ p.1 p.2

private theorem Pot_approx (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (ε : ℝ) (hε : 0 < ε) :
    ∃ (U : Config k M) (B : Fin k → Config k M), PsiV C₀ σ U B ≤ PotV C₀ σ + ε := by
  have hne : (Set.range fun p : Config k M × (Fin k → Config k M) =>
      PsiV C₀ σ p.1 p.2).Nonempty := ⟨_, ⟨(C₀, fun _ => C₀), rfl⟩⟩
  have hlt : PotV C₀ σ < PotV C₀ σ + ε := by linarith
  obtain ⟨y, hy, hylt⟩ := exists_lt_of_csInf_lt hne hlt
  obtain ⟨p, rfl⟩ := hy
  exact ⟨p.1, p.2, le_of_lt hylt⟩

/-- Lemma 6 of Koutsoupias: the minimum of the expression is attained with the last
request among the points of `U`. -/
private theorem Psi_shift (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (U : Config k M) (B : Fin k → Config k M) :
    ∃ U' : Config k M, (∃ i, U' i = r) ∧
      PsiV C₀ (σ ++ [r]) U' B ≤ PsiV C₀ (σ ++ [r]) U B := by
  classical
  obtain ⟨i, hi⟩ := wfU_step_self k hk M C₀ σ r U
  refine ⟨Function.update U i r, ⟨i, Function.update_self _ _ _⟩, ?_⟩
  have hdiff : (∑ i', (workFnU C₀ (σ ++ [r]) (B i')
        - ∑ j, dist (Function.update U i r i') (B i' j)))
      - (∑ i', (workFnU C₀ (σ ++ [r]) (B i') - ∑ j, dist (U i') (B i' j)))
      = (∑ j, dist (U i) (B i j)) - (∑ j, dist r (B i j)) := by
    have h := sum_diff_single
      (fun i' => workFnU C₀ (σ ++ [r]) (B i')
        - ∑ j, dist (Function.update U i r i') (B i' j))
      (fun i' => workFnU C₀ (σ ++ [r]) (B i') - ∑ j, dist (U i') (B i' j)) i
      (fun i' hi' => by
        show workFnU C₀ (σ ++ [r]) (B i')
            - ∑ j, dist (Function.update U i r i') (B i' j)
          = workFnU C₀ (σ ++ [r]) (B i') - ∑ j, dist (U i') (B i' j)
        rw [Function.update_of_ne hi'])
    rw [h]
    simp only [Function.update_self]
    ring
  have htri : (∑ j, dist (U i) (B i j)) - (∑ j, dist r (B i j)) ≤ (k : ℝ) * dist r (U i) := by
    have hpt : ∀ j : Fin k, dist (U i) (B i j) - dist r (B i j) ≤ dist r (U i) := by
      intro j
      have := dist_triangle (U i) r (B i j)
      rw [dist_comm (U i) r] at this
      linarith
    calc (∑ j, dist (U i) (B i j)) - (∑ j, dist r (B i j))
        = ∑ j, (dist (U i) (B i j) - dist r (B i j)) := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ _j : Fin k, dist r (U i) := Finset.sum_le_sum fun j _ => hpt j
      _ = (k : ℝ) * dist r (U i) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp [mul_comm]
  rw [PsiV, PsiV, hi]
  have hupd : workFnU C₀ (σ ++ [r]) (Function.update U i r)
      = workFnU C₀ (σ ++ [r]) (Function.update U i r) := rfl
  nlinarith [hdiff, htri]

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

private theorem Pot_le_opt (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : PotV C₀ σ ≤ 2 * (k : ℝ) * offlineCost C₀ σ := by
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  obtain ⟨X, hX⟩ := workFn_approx_offlineCost k hk M C₀ σ (ε / (2 * (k : ℝ) + 1))
    (by positivity)
  have hPsi : PsiV C₀ σ X (fun _ => X) ≤ 2 * (k : ℝ) * workFnU C₀ σ X := by
    rw [PsiV]
    have h1 : ∑ i, (workFnU C₀ σ ((fun _ => X) i) - ∑ j, dist (X i) ((fun _ => X) i j))
        ≤ ∑ _i : Fin k, workFnU C₀ σ X := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h2 : (0:ℝ) ≤ ∑ j, dist (X i) (X j) := Finset.sum_nonneg fun j _ => dist_nonneg
      show workFnU C₀ σ X - ∑ j, dist (X i) (X j) ≤ workFnU C₀ σ X
      linarith
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have h3 : 2 * (k : ℝ) * workFnU C₀ σ X
        = (k : ℝ) * workFnU C₀ σ X + (k : ℝ) * workFnU C₀ σ X := by ring
    linarith
  have hle := Pot_le k hk M C₀ σ X (fun _ => X)
  have hwf := wfU_self C₀ σ X
  have hscale : 2 * (k : ℝ) * (ε / (2 * (k : ℝ) + 1)) ≤ ε := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith [hle, hPsi, hwf, hX, hscale]

/-- The change in the potential dominates the extended cost, up to `3ε`. -/
private theorem step_bound (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (ε : ℝ) (hε : 0 < ε) (X : Config k M) :
    workFnU C₀ (σ ++ [r]) X - workFnU C₀ σ X
      ≤ PotV C₀ (σ ++ [r]) - PotV C₀ σ + 3 * ε := by
  classical
  obtain ⟨A, hA⟩ := exists_min_approx k hk M C₀ σ r ε hε
  obtain ⟨hA', hAmax⟩ := wfU_duality_approx k hk M C₀ σ r A ε hA
  obtain ⟨U, B, hUB⟩ := Pot_approx k hk M C₀ (σ ++ [r]) ε hε
  obtain ⟨U', ⟨i₀, hi₀⟩, hU'⟩ := Psi_shift k hk M C₀ σ r U B
  set B' : Fin k → Config k M := Function.update B i₀ A with hB'def
  have hB'i : B' i₀ = A := by rw [hB'def]; exact Function.update_self _ _ _
  have hB'ne : ∀ i, i ≠ i₀ → B' i = B i := by
    intro i hi; rw [hB'def]; exact Function.update_of_ne hi _ _
  -- substituting `A` at index `i₀` costs at most `ε`
  have hsub : PsiV C₀ (σ ++ [r]) U' B' ≤ PsiV C₀ (σ ++ [r]) U' B + ε := by
    have hdiff : (∑ i, (workFnU C₀ (σ ++ [r]) (B' i) - ∑ j, dist (U' i) (B' i j)))
        - (∑ i, (workFnU C₀ (σ ++ [r]) (B i) - ∑ j, dist (U' i) (B i j)))
        = (workFnU C₀ (σ ++ [r]) (B' i₀) - ∑ j, dist (U' i₀) (B' i₀ j))
          - (workFnU C₀ (σ ++ [r]) (B i₀) - ∑ j, dist (U' i₀) (B i₀ j)) :=
      sum_diff_single _ _ i₀ (fun i hi => by
        show workFnU C₀ (σ ++ [r]) (B' i) - ∑ j, dist (U' i) (B' i j)
          = workFnU C₀ (σ ++ [r]) (B i) - ∑ j, dist (U' i) (B i j)
        rw [hB'ne i hi])
    rw [hB'i, hi₀] at hdiff
    have hbound := hA' (B i₀)
    rw [PsiV, PsiV]
    linarith
  have hchain : PsiV C₀ (σ ++ [r]) U' B' ≤ PotV C₀ (σ ++ [r]) + 2 * ε := by linarith
  -- the potential at the old work function is at most the same expression
  have hold := Pot_le k hk M C₀ σ U' B'
  -- the difference of the two expressions dominates the increment at `A`
  have hmonoU := wfU_mono k hk M C₀ σ r U'
  have hmonoB : ∀ i : Fin k, (0:ℝ) ≤ workFnU C₀ (σ ++ [r]) (B' i) - workFnU C₀ σ (B' i) := by
    intro i
    have := wfU_mono k hk M C₀ σ r (B' i)
    linarith
  have hsingle : workFnU C₀ (σ ++ [r]) (B' i₀) - workFnU C₀ σ (B' i₀)
      ≤ ∑ i, (workFnU C₀ (σ ++ [r]) (B' i) - workFnU C₀ σ (B' i)) :=
    Finset.single_le_sum (fun i _ => hmonoB i) (Finset.mem_univ i₀)
  rw [hB'i] at hsingle
  have hPsidiff : PsiV C₀ (σ ++ [r]) U' B' - PsiV C₀ σ U' B'
      = (k : ℝ) * (workFnU C₀ (σ ++ [r]) U' - workFnU C₀ σ U')
        + ∑ i, (workFnU C₀ (σ ++ [r]) (B' i) - workFnU C₀ σ (B' i)) := by
    have hs : ∑ i, (workFnU C₀ (σ ++ [r]) (B' i) - ∑ j, dist (U' i) (B' i j))
        - ∑ i, (workFnU C₀ σ (B' i) - ∑ j, dist (U' i) (B' i j))
        = ∑ i, (workFnU C₀ (σ ++ [r]) (B' i) - workFnU C₀ σ (B' i)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [PsiV, PsiV]
    linarith
  have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkterm : (0:ℝ) ≤ (k : ℝ) * (workFnU C₀ (σ ++ [r]) U' - workFnU C₀ σ U') := by
    apply mul_nonneg hk0; linarith
  have hAmaxX := hAmax X
  linarith

/-- **The total growth of the unordered work function is at most `2k` times the offline
optimum**, at injective configurations. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (C₀ : Config k M) :
    ∃ c : ℝ, ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M, Function.Injective X →
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ 2 * (k : ℝ) * offlineCost C₀ σ + c := by
  classical
  refine ⟨2 * (k : ℝ) * (∑ j, dist (C₀ ⟨0, hk⟩) (C₀ j)) + 3, fun σ => ?_⟩
  refine ⟨fun t => (PotV C₀ (σ.take (t + 1)) - PotV C₀ (σ.take t))
      + 3 * ((1:ℝ) / 2 ^ (t + 1)), ?_, ?_⟩
  · intro t ht X _
    show workFnU C₀ (σ.take (t + 1)) X
      ≤ workFnU C₀ (σ.take t) X
        + ((PotV C₀ (σ.take (t + 1)) - PotV C₀ (σ.take t)) + 3 * ((1:ℝ) / 2 ^ (t + 1)))
    have hts : σ.take (t + 1) = σ.take t ++ [σ[t]] := take_succ_eq σ t ht
    have h := step_bound k hk M C₀ (σ.take t) σ[t] ((1:ℝ) / 2 ^ (t + 1)) (by positivity) X
    rw [← hts] at h
    linarith
  · show (∑ t ∈ Finset.range σ.length,
        ((PotV C₀ (σ.take (t + 1)) - PotV C₀ (σ.take t)) + 3 * ((1:ℝ) / 2 ^ (t + 1))))
      ≤ 2 * (k : ℝ) * offlineCost C₀ σ
        + (2 * (k : ℝ) * (∑ j, dist (C₀ ⟨0, hk⟩) (C₀ j)) + 3)
    have hsplit : ∑ t ∈ Finset.range σ.length,
        ((PotV C₀ (σ.take (t + 1)) - PotV C₀ (σ.take t)) + 3 * ((1:ℝ) / 2 ^ (t + 1)))
        = (∑ t ∈ Finset.range σ.length, (PotV C₀ (σ.take (t + 1)) - PotV C₀ (σ.take t)))
          + 3 * ∑ t ∈ Finset.range σ.length, ((1:ℝ) / 2 ^ (t + 1)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have htel : ∑ t ∈ Finset.range σ.length,
        (PotV C₀ (σ.take (t + 1)) - PotV C₀ (σ.take t)) = PotV C₀ σ - PotV C₀ [] := by
      rw [Finset.sum_range_sub (fun t => PotV C₀ (σ.take t)) σ.length, List.take_length,
        List.take_zero]
    have hgeom := geom_half_le_one σ.length
    have hopt := Pot_le_opt k hk M C₀ σ
    have hge := Pot_ge k hk M C₀ ([] : List M)
    rw [hsplit, htel]
    linarith
