-- Prove2me | solution 1 for KServer.ckPotK_step_antipode
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-07T13:22:55.788893+00:00
-- url     : https://prove2.me/submissions/68e78add-256d-41ed-a818-9699493b1b0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential_k
import Theorems.Thm_KServer_ckPotK_anchor_at_request

/-!
Reduction of `KServer.ckPotK_step_antipode` to `KServer.ckPotK_anchor_at_request`.

If the minimum defining the potential after the request is attained at an anchor tuple
whose last coordinate is the request, then every configuration of that tuple's chain except
the top one contains the (left copy of the) request, so appending the request does not
change the work function there, while the top configuration is exactly the coalesced
antipodal configuration `r̄^k` appearing on the left-hand side.  The chain therefore
telescopes to the left-hand side exactly.
-/

open KServer

namespace CKStepAux

variable {k : ℕ} {M : Type*} [MetricSpace M]

/-- The cost of the offline solution given by the schedule `S` and a final move to `X`. -/
noncomputable def schedCost (σ : List M) (S : ℕ → Config k M) (X : Config k M) : ℝ :=
  (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))) + moveCost (S σ.length) X

theorem moveCost_nonneg (C C' : Config k M) : 0 ≤ moveCost C C' :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

theorem moveCost_self (C : Config k M) : moveCost C C = 0 := by
  simp [moveCost]

theorem moveCost_triangle (C C' C'' : Config k M) :
    moveCost C C'' ≤ moveCost C C' + moveCost C' C'' := by
  simp only [moveCost, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

theorem schedCost_nonneg (σ : List M) (S : ℕ → Config k M) (X : Config k M) :
    0 ≤ schedCost σ S X :=
  add_nonneg (Finset.sum_nonneg fun _ _ => moveCost_nonneg _ _) (moveCost_nonneg _ _)

theorem exists_servesFrom (hk : 1 ≤ k) (C₀ : Config k M) (σ : List M) :
    ∃ S : ℕ → Config k M, ServesFrom C₀ σ S := by
  have h0 : (0 : ℕ) < k := hk
  refine ⟨fun t => if t = 0 then C₀ else fun _ => σ.getD (t - 1) (C₀ ⟨0, h0⟩), by simp, ?_⟩
  intro j
  refine ⟨⟨0, h0⟩, ?_⟩
  have hne : ((j : ℕ) + 1) ≠ 0 := Nat.succ_ne_zero _
  simp only [hne, if_false, Nat.add_sub_cancel]
  exact List.getD_eq_getElem _ _ j.2

theorem workFn_le_schedCost {C₀ : Config k M} {σ : List M} {S : ℕ → Config k M}
    (hS : ServesFrom C₀ σ S) (X : Config k M) : workFn C₀ σ X ≤ schedCost σ S X := by
  refine csInf_le ⟨0, ?_⟩ ⟨S, hS, rfl⟩
  rintro c ⟨S', _, rfl⟩
  exact schedCost_nonneg _ _ _

theorem le_workFn (hk : 1 ≤ k) {C₀ : Config k M} {σ : List M} {X : Config k M} {c : ℝ}
    (h : ∀ S : ℕ → Config k M, ServesFrom C₀ σ S → c ≤ schedCost σ S X) :
    c ≤ workFn C₀ σ X := by
  obtain ⟨S, hS⟩ := exists_servesFrom hk C₀ σ
  refine le_csInf ⟨schedCost σ S X, ⟨S, hS, rfl⟩⟩ ?_
  rintro b ⟨S', hS', rfl⟩
  exact h S' hS'

theorem workFnU_le_of_perm (C₀ : Config k M) (σ : List M) (X : Config k M)
    (π : Equiv.Perm (Fin k)) : workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) _

theorem le_workFnU {C₀ : Config k M} {σ : List M} {X : Config k M} {c : ℝ}
    (h : ∀ π : Equiv.Perm (Fin k), c ≤ workFn C₀ σ (X ∘ π)) : c ≤ workFnU C₀ σ X :=
  le_ciInf h

theorem servesFrom_of_snoc {C₀ : Config k M} {σ : List M} {r : M} {S : ℕ → Config k M}
    (hS : ServesFrom C₀ (σ ++ [r]) S) : ServesFrom C₀ σ S := by
  refine ⟨hS.1, fun j => ?_⟩
  have hj : (j : ℕ) < (σ ++ [r]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  obtain ⟨i, hi⟩ := hS.2 ⟨j, hj⟩
  refine ⟨i, ?_⟩
  rw [hi]
  simp [List.get_eq_getElem, List.getElem_append_left j.2]

/-- Monotonicity of the work function in the request sequence. -/
theorem workFn_le_workFn_snoc (hk : 1 ≤ k) {C₀ : Config k M} {σ : List M} {r : M}
    (X : Config k M) : workFn C₀ σ X ≤ workFn C₀ (σ ++ [r]) X := by
  refine le_workFn hk fun S hS => ?_
  have hlen : (σ ++ [r]).length = σ.length + 1 := by simp
  calc workFn C₀ σ X ≤ schedCost σ S X := workFn_le_schedCost (servesFrom_of_snoc hS) X
    _ ≤ schedCost (σ ++ [r]) S X := by
        simp only [schedCost, hlen, Finset.sum_range_succ]
        have h1 := moveCost_triangle (S σ.length) (S (σ.length + 1)) X
        linarith

theorem workFnU_le_workFnU_snoc (hk : 1 ≤ k) {C₀ : Config k M} {σ : List M} {r : M}
    (X : Config k M) : workFnU C₀ σ X ≤ workFnU C₀ (σ ++ [r]) X :=
  le_ciInf fun π => le_trans (workFnU_le_of_perm _ _ _ π) (workFn_le_workFn_snoc hk _)

/-- A configuration that already contains the last request sees the same work function
value before and after that request. -/
theorem workFn_snoc_of_mem (hk : 1 ≤ k) {C₀ : Config k M} {σ : List M} {r : M}
    {X : Config k M} (hX : ∃ i, X i = r) :
    workFn C₀ (σ ++ [r]) X = workFn C₀ σ X := by
  refine le_antisymm ?_ (workFn_le_workFn_snoc hk X)
  refine le_workFn hk fun S hS => ?_
  classical
  set S' : ℕ → Config k M := fun t => if t ≤ σ.length then S t else X with hS'
  have hserves : ServesFrom C₀ (σ ++ [r]) S' := by
    refine ⟨by simp [hS', hS.1], fun j => ?_⟩
    have hjlt : (j : ℕ) < σ.length + 1 := by simpa using j.2
    rcases Nat.lt_or_ge (j : ℕ) σ.length with hj | hj
    · obtain ⟨i, hi⟩ := hS.2 ⟨j, hj⟩
      refine ⟨i, ?_⟩
      have hle : ((j : ℕ) + 1) ≤ σ.length := hj
      simp only [hS', hle, if_true]
      rw [hi]
      simp [List.get_eq_getElem, List.getElem_append_left hj]
    · have hj' : (j : ℕ) = σ.length := le_antisymm (by omega) hj
      obtain ⟨i, hi⟩ := hX
      refine ⟨i, ?_⟩
      have hnot : ¬ ((j : ℕ) + 1 ≤ σ.length) := by omega
      simp only [hS', hnot, if_false]
      rw [hi]
      simp [List.get_eq_getElem, hj', List.getElem_append_right]
  refine le_trans (workFn_le_schedCost hserves X) ?_
  have hlen : (σ ++ [r]).length = σ.length + 1 := by simp
  have hstep : ∀ j ∈ Finset.range σ.length, moveCost (S' j) (S' (j + 1)) =
      moveCost (S j) (S (j + 1)) := by
    intro j hj
    have hj' : j < σ.length := Finset.mem_range.mp hj
    have h1 : j ≤ σ.length := le_of_lt hj'
    have h2 : j + 1 ≤ σ.length := hj'
    simp [hS', h1, h2]
  have hlast : S' σ.length = S σ.length := by simp [hS']
  have hlast' : S' (σ.length + 1) = X := by simp [hS']
  simp only [schedCost, hlen, Finset.sum_range_succ, Finset.sum_congr rfl hstep, hlast, hlast',
    moveCost_self, add_zero]
  exact le_refl _

theorem workFnU_snoc_of_mem (hk : 1 ≤ k) {C₀ : Config k M} {σ : List M} {r : M}
    {X : Config k M} (hX : ∃ i, X i = r) :
    workFnU C₀ (σ ++ [r]) X = workFnU C₀ σ X := by
  refine le_antisymm (le_workFnU fun π => ?_) (workFnU_le_workFnU_snoc hk X)
  have hX' : ∃ i, (X ∘ π) i = r := by
    obtain ⟨i, hi⟩ := hX
    exact ⟨π.symm i, by simpa using hi⟩
  calc workFnU C₀ (σ ++ [r]) X ≤ workFn C₀ (σ ++ [r]) (X ∘ π) := workFnU_le_of_perm _ _ _ _
    _ = workFn C₀ σ (X ∘ π) := workFn_snoc_of_mem hk hX'

/-! ### The chain of an anchor tuple whose last coordinate is the request -/

variable {N : Type}

/-- The last index of `Fin k`. -/
def lastIdx (k : ℕ) (hk : 1 ≤ k) : Fin k := ⟨k - 1, by omega⟩

theorem le_lastIdx (hk : 1 ≤ k) (i : Fin k) : (i : ℕ) ≤ (lastIdx k hk : ℕ) := by
  have := i.2; simp only [lastIdx]; omega

theorem ckConfigK_lastIdx (hk : 1 ≤ k) {M : Type} {x : Fin k → M} {r : M}
    (hx : x (lastIdx k hk) = r) :
    ckConfigK x (lastIdx k hk) = fun _ : Fin k => (Sum.inr r : M ⊕ M) := by
  funext j
  simp only [ckConfigK, hx, le_lastIdx hk j, if_true]

theorem ckConfigK_mem_of_lt (hk : 1 ≤ k) {M : Type} {x : Fin k → M} {r : M}
    (hx : x (lastIdx k hk) = r) {i : Fin k} (hi : i ≠ lastIdx k hk) :
    ∃ j, ckConfigK x i j = (Sum.inl r : M ⊕ M) := by
  refine ⟨lastIdx k hk, ?_⟩
  have hlt : ¬ ((lastIdx k hk : ℕ) ≤ (i : ℕ)) := by
    have h1 : (i : ℕ) ≤ k - 1 := le_lastIdx hk i
    have h2 : (i : ℕ) ≠ k - 1 := fun h => hi (Fin.ext h)
    simp only [lastIdx]
    omega
  simp only [ckConfigK, hlt, if_false, hx]

end CKStepAux

open CKStepAux in
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (l : List M) (r : M) :
    @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (C₀ i))
        ((l ++ [r]).map Sum.inl) (fun _ => Sum.inr r)
      - @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (C₀ i))
        (l.map Sum.inl) (fun _ => Sum.inr r)
      ≤ ckPotK k M Δ hΔ0 hΔ C₀ (l ++ [r]) - ckPotK k M Δ hΔ0 hΔ C₀ l := by
  classical
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  -- the work function of the extension
  set W : List M → Config k (M ⊕ M) → ℝ := fun σ X =>
    @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (C₀ i))
      (σ.map Sum.inl) X with hW
  have hmap : ((l ++ [r]).map Sum.inl : List (M ⊕ M)) = (l.map Sum.inl) ++ [Sum.inl r] := by
    simp
  have hF2 : ∀ X : Config k (M ⊕ M), (∃ j, X j = Sum.inl r) → W (l ++ [r]) X = W l X := by
    intro X hX
    simp only [hW, hmap]
    exact workFnU_snoc_of_mem hk hX
  -- the anchor tuple provided by the child lemma
  obtain ⟨x, hxlast, hxmin⟩ := ckPotK_anchor_at_request k hk M Δ hΔ0 hΔ C₀ l r
  have hxlast' : x (lastIdx k hk) = r := hxlast
  have hpot : ∀ σ : List M, ckPotAtK k M Δ hΔ0 hΔ C₀ σ x
      = W σ (fun j => Sum.inl (x j)) + ∑ i : Fin k, W σ (ckConfigK x i) := fun σ => rfl
  have hbase : ∃ j, (fun j => Sum.inl (x j) : Config k (M ⊕ M)) j = Sum.inl r :=
    ⟨lastIdx k hk, by simp [hxlast']⟩
  have hbase_eq : W (l ++ [r]) (fun j => Sum.inl (x j)) = W l (fun j => Sum.inl (x j)) :=
    hF2 _ hbase
  have hchain : ∀ i : Fin k, i ≠ lastIdx k hk →
      W (l ++ [r]) (ckConfigK x i) - W l (ckConfigK x i) = 0 := by
    intro i hi
    have := hF2 _ (ckConfigK_mem_of_lt hk hxlast' hi)
    linarith
  have htop : ckConfigK x (lastIdx k hk) = fun _ : Fin k => (Sum.inr r : M ⊕ M) :=
    ckConfigK_lastIdx hk hxlast'
  have hsum : (∑ i : Fin k, W (l ++ [r]) (ckConfigK x i))
      - (∑ i : Fin k, W l (ckConfigK x i))
      = W (l ++ [r]) (fun _ => Sum.inr r) - W l (fun _ => Sum.inr r) := by
    have h1 : (∑ i : Fin k, W (l ++ [r]) (ckConfigK x i))
        - (∑ i : Fin k, W l (ckConfigK x i))
        = ∑ i : Fin k, (W (l ++ [r]) (ckConfigK x i) - W l (ckConfigK x i)) :=
      (Finset.sum_sub_distrib _ _).symm
    rw [h1]
    have h2 := Finset.sum_eq_single_of_mem (s := (Finset.univ : Finset (Fin k)))
      (f := fun i => W (l ++ [r]) (ckConfigK x i) - W l (ckConfigK x i)) (lastIdx k hk)
      (Finset.mem_univ _) (fun i _ hi => hchain i hi)
    rw [h2]
    simp only [htop]
  have hstep : ckPotAtK k M Δ hΔ0 hΔ C₀ (l ++ [r]) x - ckPotAtK k M Δ hΔ0 hΔ C₀ l x
      = W (l ++ [r]) (fun _ => Sum.inr r) - W l (fun _ => Sum.inr r) := by
    rw [hpot, hpot]
    linarith [hbase_eq, hsum]
  have hle : ckPotK k M Δ hΔ0 hΔ C₀ l ≤ ckPotAtK k M Δ hΔ0 hΔ C₀ l x :=
    ckPotK_le k M Δ hΔ0 hΔ C₀ l x
  have hgoal : W (l ++ [r]) (fun _ => Sum.inr r) - W l (fun _ => Sum.inr r)
      ≤ ckPotK k M Δ hΔ0 hΔ C₀ (l ++ [r]) - ckPotK k M Δ hΔ0 hΔ C₀ l := by
    rw [← hxmin]; linarith
  exact hgoal
