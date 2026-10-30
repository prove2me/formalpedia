-- Prove2me | solution 1 for KServer.kserver_distributional_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T01:47:59.436131+00:00
-- url     : https://prove2.me/submissions/17ec4286-dc32-4834-b46d-64b1a483dce9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_encoding
import Theorems.Thm_KServer_schedule_exists
import Theorems.Thm_KServer_exists_lazy_injective_algorithm
import Theorems.Thm_KServer_server_to_evader_reduction
import Theorems.Thm_KServer_evader_to_server_offline
import Theorems.Thm_KServer_mss_randomized_lower_bound

namespace KServer

section Helpers

variable {k : ℕ} {M : Type} [MetricSpace M]

private theorem moveCost_nonneg' (C D : Config k M) : 0 ≤ moveCost C D :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

private theorem moveCost_triangle' (C D E : Config k M) :
    moveCost C E ≤ moveCost C D + moveCost D E := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

/-- Replacing the head of a trajectory costs at most one extra move. -/
private theorem sum_replace_head' (f : ℕ → Config k M) (C : Config k M) (n : ℕ) :
    ∑ j ∈ Finset.range n, moveCost (if j = 0 then C else f j) (f (j + 1))
      ≤ moveCost C (f 0) + ∑ j ∈ Finset.range n, moveCost (f j) (f (j + 1)) := by
  cases n with
  | zero => simpa using moveCost_nonneg' C (f 0)
  | succ m =>
    rw [Finset.sum_range_succ' (fun j => moveCost (if j = 0 then C else f j) (f (j + 1))) m,
      Finset.sum_range_succ' (fun j => moveCost (f j) (f (j + 1))) m]
    have hz : ∀ i : ℕ, (if i + 1 = 0 then C else f (i + 1)) = f (i + 1) := fun i => by simp
    simp only [hz, if_true]
    have := moveCost_triangle' C (f 0) (f (0 + 1))
    linarith

private theorem offlineCost_nonneg' (hk : 1 ≤ k) (C₀ : Config k M) (σ : List M) :
    0 ≤ offlineCost C₀ σ := by
  refine le_csInf ?_ ?_
  · obtain ⟨S, hS⟩ := schedule_exists k hk M C₀ σ
    exact ⟨_, ⟨S, hS, rfl⟩⟩
  · rintro x ⟨S, _, rfl⟩
    exact Finset.sum_nonneg fun j _ => moveCost_nonneg' _ _

/-- Moving the initial configuration changes the optimal offline cost by at most one move. -/
private theorem offlineCost_shift' (hk : 1 ≤ k) (C₀ C₁ : Config k M) (σ : List M) :
    offlineCost C₀ σ ≤ offlineCost C₁ σ + moveCost C₀ C₁ := by
  have hbdd : BddBelow {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
      c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))} := by
    refine ⟨0, ?_⟩
    rintro x ⟨S, _, rfl⟩
    exact Finset.sum_nonneg fun j _ => moveCost_nonneg' _ _
  have hne : {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₁ σ S ∧
      c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))}.Nonempty := by
    obtain ⟨S, hS⟩ := schedule_exists k hk M C₁ σ
    exact ⟨_, ⟨S, hS, rfl⟩⟩
  rw [← sub_le_iff_le_add]
  refine le_csInf hne ?_
  rintro x ⟨S, hS, rfl⟩
  rw [sub_le_iff_le_add]
  have hserves : ServesFrom C₀ σ (fun j => if j = 0 then C₀ else S j) := by
    refine ⟨by simp, ?_⟩
    intro j
    obtain ⟨i, hi⟩ := hS.2 j
    exact ⟨i, by simpa using hi⟩
  have hmem : (∑ j ∈ Finset.range σ.length,
        moveCost (if j = 0 then C₀ else S j) (if j + 1 = 0 then C₀ else S (j + 1)))
      ∈ {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
        c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))} :=
    ⟨_, hserves, rfl⟩
  refine le_trans (csInf_le hbdd hmem) ?_
  have hS0 : S 0 = C₁ := hS.1
  calc ∑ j ∈ Finset.range σ.length,
          moveCost (if j = 0 then C₀ else S j) (if j + 1 = 0 then C₀ else S (j + 1))
      = ∑ j ∈ Finset.range σ.length, moveCost (if j = 0 then C₀ else S j) (S (j + 1)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp
    _ ≤ moveCost C₀ (S 0) + ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
        sum_replace_head' S C₀ σ.length
    _ = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) + moveCost C₀ C₁ := by
        rw [hS0]; ring

/-- Restart an online algorithm from a different initial configuration. -/
private noncomputable def restart' (B : OnlineAlgorithm k M) (C : Config k M) :
    OnlineAlgorithm k M where
  conf l := if l = [] then C else B.conf l
  serves l r := by
    have h : (l ++ [r]) ≠ [] := by simp
    simpa [h] using B.serves l r

private theorem restart_conf_nil' (B : OnlineAlgorithm k M) (C : Config k M) :
    (restart' B C).conf [] = C := by simp [restart']

private theorem restart_cost_le' (B : OnlineAlgorithm k M) (C : Config k M) (σ : List M) :
    (restart' B C).cost σ ≤ B.cost σ + moveCost C (B.conf []) := by
  unfold OnlineAlgorithm.cost
  have key : ∀ j ∈ Finset.range σ.length,
      moveCost ((restart' B C).conf (σ.take j)) ((restart' B C).conf (σ.take (j + 1)))
        = moveCost (if j = 0 then C else B.conf (σ.take j)) (B.conf (σ.take (j + 1))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 : (σ.take (j + 1)) ≠ [] := by
      simp only [ne_eq, List.take_eq_nil_iff, not_or]
      refine ⟨by omega, ?_⟩
      intro h; rw [h] at hj; simp at hj
    have h2 : (restart' B C).conf (σ.take (j + 1)) = B.conf (σ.take (j + 1)) := by
      simp [restart', h1]
    rw [h2]
    congr 1
    by_cases hj0 : j = 0
    · subst hj0; simp [restart']
    · have h3 : (σ.take j) ≠ [] := by
        simp only [ne_eq, List.take_eq_nil_iff, not_or]
        refine ⟨hj0, ?_⟩
        intro h; rw [h] at hj; simp at hj
      simp [restart', h3, hj0]
  rw [Finset.sum_congr rfl key]
  have h := sum_replace_head' (fun j => B.conf (σ.take j)) C σ.length
  simp only [List.take_zero] at h
  linarith

end Helpers

/-- A serving offline trajectory can be followed on its prescribed input by
an online algorithm; on other inputs it serves with the first server. -/
private noncomputable def followSchedule {k : ℕ} (hk : 1 ≤ k)
    {M : Type} [MetricSpace M] (C₀ : Config k M) (τ : List M)
    (S : ℕ → Config k M) (hS : ServesFrom C₀ τ S) : OnlineAlgorithm k M := by
  classical
  refine { conf := fun l => if l.IsPrefix τ then S l.length
    else fun _ => l.getLastD (C₀ ⟨0, by omega⟩), serves := ?_ }
  intro l r
  by_cases hp : (l ++ [r]).IsPrefix τ
  · have hlen : l.length < τ.length := by
      have := hp.length_le
      simp only [List.length_append, List.length_singleton] at this
      omega
    obtain ⟨i, hi⟩ := hS.2 ⟨l.length, hlen⟩
    refine ⟨i, ?_⟩
    simp only [if_pos hp, List.length_append, List.length_singleton]
    have heq := hp.getElem (i := l.length) (by simp)
    have hr : τ[l.length] = r := by simpa using heq.symm
    simpa [List.get_eq_getElem, hr] using hi
  · refine ⟨⟨0, by omega⟩, ?_⟩
    simp [hp]

private theorem offline_lower_of_all_online {k : ℕ} (hk : 1 ≤ k)
    {M : Type} [MetricSpace M] (C₀ : Config k M) (τ : List M) (L : ℝ)
    (hL : ∀ A : OnlineAlgorithm k M, A.conf [] = C₀ → L ≤ A.cost τ) :
    L ≤ offlineCost C₀ τ := by
  classical
  unfold offlineCost
  refine le_csInf ?_ ?_
  · obtain ⟨S, hS⟩ := schedule_exists k hk M C₀ τ
    exact ⟨_, S, hS, rfl⟩
  · rintro x ⟨S, hS, rfl⟩
    let A := followSchedule hk C₀ τ S hS
    have hA : A.conf [] = C₀ := by simpa [A, followSchedule] using hS.1
    have hconf (j : ℕ) (hj : j ≤ τ.length) : A.conf (τ.take j) = S j := by
      simp [A, followSchedule, List.take_prefix, List.length_take, min_eq_left hj]
    have hcost : A.cost τ = ∑ j ∈ Finset.range τ.length, moveCost (S j) (S (j + 1)) := by
      unfold OnlineAlgorithm.cost
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      rw [hconf j (by omega), hconf (j + 1) (by omega)]
    simpa [hcost] using hL A hA

private theorem evader_offline_le_cost {M : Type} [MetricSpace M]
    (E : EvaderAlgorithm M) (σ : List (Set M)) : evaderOfflineCost (E.pos []) σ ≤ E.cost σ := by
  have hbdd : BddBelow {c : ℝ | ∃ P : ℕ → M, EvaderServes (E.pos []) σ P ∧
      c = ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))} := by
    refine ⟨0, ?_⟩
    rintro x ⟨P, _, rfl⟩
    exact Finset.sum_nonneg fun _ _ => dist_nonneg
  apply csInf_le hbdd
  refine ⟨fun j => E.pos (σ.take j), ⟨by simp, ?_⟩, rfl⟩
  intro j hj
  change E.pos (σ.take (j.val + 1)) ∈ σ.get j
  rw [List.take_succ_eq_append_getElem j.isLt]
  exact E.serves (σ.take j) (σ.get j) hj

/-- Quantitative form of the complement encoding, including arbitrary starts. -/
private theorem encoding_comparison (k : ℕ) (hk2 : 2 ≤ k)
    (M : Type) [MetricSpace M] [Fintype M] (hcard : Fintype.card M = k + 1)
    (C₀ : Config k M) :
    ∃ (R : ℕ) (x : M) (D : ℝ), 0 ≤ D ∧
      (∀ σ : List (Set M), (∀ S ∈ σ, S.Nonempty) →
        offlineCost C₀ (encSeq M R σ) ≤ evaderOfflineCost x σ + D) ∧
      (∀ A : OnlineAlgorithm k M, A.conf [] = C₀ →
        ∃ E : EvaderAlgorithm M, E.pos [] = x ∧
          ∀ σ : List (Set M), E.cost σ ≤ 4 * A.cost (encSeq M R σ) + D) := by
  classical
  have hk1 : 1 ≤ k := by omega
  -- a reference injective initial configuration and the point it misses
  obtain ⟨e⟩ : Nonempty (M ≃ Fin (k + 1)) := by
    refine ⟨(Fintype.equivFinOfCardEq hcard)⟩
  set C₁ : Config k M := fun i => e.symm i.castSucc with hC₁
  set x₁ : M := e.symm (Fin.last k) with hx₁def
  have hC₁inj : Function.Injective C₁ := by
    intro i j hij
    have := e.symm.injective hij
    exact Fin.castSucc_injective k this
  have hx₁ : x₁ ∉ Set.range C₁ := by
    rintro ⟨i, hi⟩
    have := e.symm.injective hi
    have h2 := congrArg Fin.val this
    simp [Fin.last] at h2
    omega
  have hmiss : ∀ y : M, y ∉ Set.range C₁ → y = x₁ := by
    intro y hy
    by_contra hne
    apply hy
    have hlt : (e y).val < k := by
      rcases Nat.lt_or_ge (e y).val k with h | h
      · exact h
      · exfalso
        apply hne
        have : e y = Fin.last k := by
          apply Fin.ext
          have := (e y).isLt
          simp [Fin.last]
          omega
        rw [hx₁def, ← this, Equiv.symm_apply_apply]
    exact ⟨⟨(e y).val, hlt⟩, by
      rw [hC₁]
      simp only
      rw [show (⟨(e y).val, hlt⟩ : Fin k).castSucc = e y from by apply Fin.ext; simp]
      exact e.symm_apply_apply y⟩
  -- the geometry of the finite space
  have h1card : 1 < Fintype.card M := by omega
  haveI : Nontrivial M := Fintype.one_lt_card_iff_nontrivial.mp h1card
  obtain ⟨x', y', hx'y'⟩ := exists_pair_ne M
  have hne2 : (Finset.univ.filter (fun q : M × M => q.1 ≠ q.2)).Nonempty :=
    ⟨(x', y'), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'y'⟩⟩
  set δ : ℝ := (Finset.univ.filter (fun q : M × M => q.1 ≠ q.2)).inf' hne2
    (fun q => dist q.1 q.2) with hδdef
  have hδ : ∀ x y : M, x ≠ y → δ ≤ dist x y := by
    intro x y hxy
    have hmem : (x, y) ∈ Finset.univ.filter (fun q : M × M => q.1 ≠ q.2) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hxy
    exact Finset.inf'_le (fun q : M × M => dist q.1 q.2) hmem
  have hδ0 : 0 < δ := by
    rw [hδdef, Finset.lt_inf'_iff]
    intro q hq
    rw [Finset.mem_filter] at hq
    exact dist_pos.mpr hq.2
  have hunivne : (Finset.univ : Finset (M × M)).Nonempty :=
    ⟨(x', y'), Finset.mem_univ _⟩
  set Δ : ℝ := (Finset.univ : Finset (M × M)).sup' hunivne (fun q => dist q.1 q.2) with hΔdef
  have hΔ : ∀ x y : M, dist x y ≤ Δ := fun x y =>
    Finset.le_sup' (fun q : M × M => dist q.1 q.2) (Finset.mem_univ (x, y))
  set R : ℕ := ⌈Δ / δ⌉₊ with hRdef
  have hR : Δ ≤ R * δ := by
    rw [hRdef, ← div_le_iff₀ hδ0]
    exact Nat.le_ceil _
  let K : ℝ := moveCost C₁ C₀
  let K' : ℝ := moveCost C₀ C₁
  let D : ℝ := 4 * K + K'
  have hK : 0 ≤ K := moveCost_nonneg' _ _
  have hK' : 0 ≤ K' := moveCost_nonneg' _ _
  refine ⟨R, x₁, D, by dsimp [D]; positivity, ?_, ?_⟩
  · intro σ hσ
    have hshift := offlineCost_shift' hk1 C₀ C₁ (encSeq M R σ)
    have hoff := evader_to_server_offline k hk1 M hcard R C₁ hC₁inj x₁ hx₁ σ hσ
    dsimp [D, K']
    linarith
  · intro A hA
    let A' := restart' A C₁
    have hA' : A'.conf [] = C₁ := restart_conf_nil' A C₁
    have hinj : Function.Injective (A'.conf []) := by rw [hA']; exact hC₁inj
    obtain ⟨B, hB0, hBcost, hBinj, hBlazy, hBlazy2⟩ :=
      exists_lazy_injective_algorithm k M A' hinj
    obtain ⟨E, hEpos, hEcost⟩ :=
      server_to_evader_reduction k M hcard δ Δ hδ0 hδ hΔ R hR B hBinj hBlazy hBlazy2
    have hE0 : E.pos [] = x₁ := by
      apply hmiss
      rw [hB0, hA'] at hEpos
      exact hEpos
    refine ⟨E, hE0, ?_⟩
    intro σ
    have hrestart := restart_cost_le' A C₁ (encSeq M R σ)
    rw [hA] at hrestart
    have hdom := hBcost (encSeq M R σ)
    have henc := hEcost σ
    dsimp [D, K]
    dsimp [A'] at hdom
    nlinarith

end KServer

open KServer in
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ m : MetricSpace (Fin (k + 1)),
        ∀ (C₀ : Config k (Fin (k + 1))) (N : ℝ),
          ∃ (n : ℕ) (p : Fin n → ℝ) (σ : Fin n → List (Fin (k + 1))),
            (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
            N ≤ ∑ j, p j * @offlineCost k (Fin (k + 1)) m C₀ (σ j) ∧
            ∀ A : @OnlineAlgorithm k (Fin (k + 1)) m,
              @OnlineAlgorithm.conf k (Fin (k + 1)) m A [] = C₀ →
              c * Real.log k ^ 2 * (∑ j, p j * @offlineCost k (Fin (k + 1)) m C₀ (σ j))
                ≤ ∑ j, p j * @OnlineAlgorithm.cost k (Fin (k + 1)) m A (σ j) := by
  classical
  obtain ⟨c, hc, k₀, hmss⟩ := mss_randomized_lower_bound
  refine ⟨c / 8, by positivity, max k₀ 2, ?_⟩
  intro k hk
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hk
  have hk1 : 1 ≤ k := by omega
  obtain ⟨m, hm⟩ := hmss k (le_trans (le_max_left _ _) hk)
  letI : MetricSpace (Fin (k + 1)) := m
  refine ⟨m, ?_⟩
  intro C₀ N
  obtain ⟨R, x, D, hD, hupper, hsim⟩ :=
    encoding_comparison k hk2 (Fin (k + 1)) (Fintype.card_fin _) C₀
  let r : ℝ := c * Real.log k ^ 2
  have hlog : 0 < Real.log k := by
    apply Real.log_pos
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    linarith
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨n, p, σ, hp0, hp1, hσ, hlarge, hlower⟩ :=
    hm (max (4 * N + D) ((r + 2) * D / r))
  let τ : Fin n → List (Fin (k + 1)) := fun j => encSeq (Fin (k + 1)) R (σ j)
  let W : ℝ := ∑ j, p j * evaderOfflineCost x (σ j)
  let V : ℝ := ∑ j, p j * offlineCost C₀ (τ j)
  have avg {f g : Fin n → ℝ} {a : ℝ} (hfg : ∀ j, f j ≤ g j + a) :
      ∑ j, p j * f j ≤ (∑ j, p j * g j) + a := by
    calc
      ∑ j, p j * f j ≤ ∑ j, p j * (g j + a) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hfg j) (hp0 j)
      _ = (∑ j, p j * g j) + a := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul]
  have hVW : V ≤ W + D := avg fun j => hupper (σ j) (hσ j)
  have hreverse (j : Fin n) : evaderOfflineCost x (σ j) ≤ 4 * offlineCost C₀ (τ j) + D := by
    have hbound := offline_lower_of_all_online hk1 C₀ (τ j)
      ((evaderOfflineCost x (σ j) - D) / 4) (by
        intro A hA
        obtain ⟨E, hE0, hEcost⟩ := hsim A hA
        have hoff := evader_offline_le_cost E (σ j)
        rw [hE0] at hoff
        have hcost := hEcost (σ j)
        change E.cost (σ j) ≤ 4 * A.cost (τ j) + D at hcost
        linarith)
    linarith
  have hWV : W ≤ 4 * V + D := by
    have h := avg hreverse
    have heq : (∑ j, p j * (4 * offlineCost C₀ (τ j))) = 4 * V := by
      dsimp [V]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rwa [heq] at h
  have hWN : 4 * N + D ≤ W := le_trans (le_max_left _ _) (hlarge x)
  have hWD : (r + 2) * D ≤ r * W := by
    have h := (div_le_iff₀ hr).mp (le_trans (le_max_right _ _) (hlarge x))
    linarith
  refine ⟨n, p, τ, hp0, hp1, by change N ≤ V; linarith, ?_⟩
  intro A hA
  obtain ⟨E, hE0, hEcost⟩ := hsim A hA
  have hlow : r * W ≤ ∑ j, p j * E.cost (σ j) := by
    have h := hlower E
    rw [hE0] at h
    exact h
  have hhigh : (∑ j, p j * E.cost (σ j)) ≤ 4 * (∑ j, p j * A.cost (τ j)) + D := by
    have h := avg (fun j => hEcost (σ j))
    have heq : (∑ j, p j * (4 * A.cost (τ j))) = 4 * (∑ j, p j * A.cost (τ j)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rwa [heq] at h
  have hmul := mul_le_mul_of_nonneg_left hVW hr.le
  change c / 8 * Real.log k ^ 2 * V ≤ _
  dsimp [r] at hlow hWD hmul
  nlinarith
