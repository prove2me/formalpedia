-- Prove2me | solution 1 for KServer.randomized_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-04T21:39:19.795448+00:00
-- url     : https://prove2.me/submissions/dd9ab969-40e6-48f7-8d75-3d7629cf5074
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_encoding
import Theorems.Thm_KServer_schedule_exists
import Theorems.Thm_KServer_randomized_yao_averaging
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

/-- The reduction of the randomized `k`-server lower bound on a `(k+1)`-point space
to the corresponding lower bound for small set chasing (metrical service systems)
on the same space. -/
private theorem kserver_of_mss (k : ℕ) (hk2 : 2 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (hcard : Fintype.card M = k + 1) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hm : ∀ N : ℝ, ∃ (n : ℕ) (p : Fin n → ℝ) (σ : Fin n → List (Set M)),
      (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
      (∀ j, ∀ S ∈ σ j, S.Nonempty) ∧
      (∀ x₀ : M, N ≤ ∑ j, p j * evaderOfflineCost x₀ (σ j)) ∧
      (∀ E : EvaderAlgorithm M,
        c₀ * Real.log k ^ 2 * ∑ j, p j * evaderOfflineCost (E.pos []) (σ j)
          ≤ ∑ j, p j * E.cost (σ j)))
    (C₀ : Config k M) (A : RandomizedAlgorithm k M) (ρ : ℝ)
    (hcomp : A.IsCompetitiveFrom C₀ ρ) :
    c₀ / 4 * Real.log k ^ 2 ≤ ρ := by
  have hk1 : 1 ≤ k := by omega
  have hlog : 0 < Real.log k := by
    apply Real.log_pos
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    linarith
  have hpos : 0 < c₀ * Real.log k ^ 2 := by positivity
  -- the core estimate, for a nonnegative competitive ratio
  have core : ∀ r : ℝ, 0 ≤ r → A.IsCompetitiveFrom C₀ r → c₀ * Real.log k ^ 2 ≤ 4 * r := by
    intro r hr hcr
    classical
    obtain ⟨a, ha0, hyao⟩ := randomized_yao_averaging k M A C₀ r hr hcr
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
    -- suppose the bound fails
    by_contra hcon
    have hcon' : 4 * r < c₀ * Real.log k ^ 2 := lt_of_not_ge hcon
    set d : ℝ := c₀ * Real.log k ^ 2 - 4 * r with hddef
    have hd : 0 < d := by rw [hddef]; linarith
    set K : ℝ := moveCost C₁ C₀ with hKdef
    set K' : ℝ := moveCost C₀ C₁ with hK'def
    set Cst : ℝ := 4 * r * K' + 4 * a + 4 + 4 * K with hCstdef
    obtain ⟨n, p, σ, hp0, hp1, hSne, hOPT, hLB⟩ := hm (Cst / d + 1)
    set τ : Fin n → List M := fun j => encSeq M R (σ j) with hτdef
    obtain ⟨i, hi0, hi⟩ := hyao n p hp0 hp1 τ 1 one_pos
    set B : OnlineAlgorithm k M := A.alg i with hBdef
    set B' : OnlineAlgorithm k M := restart' B C₁ with hB'def
    have hB'0 : B'.conf [] = C₁ := restart_conf_nil' B C₁
    have hB'inj : Function.Injective (B'.conf []) := by rw [hB'0]; exact hC₁inj
    obtain ⟨Bl, hBl0, hBlcost, hBlinj, hBllazy, hBllazy2⟩ :=
      exists_lazy_injective_algorithm k M B' hB'inj
    obtain ⟨E, hEpos, hEcost⟩ :=
      server_to_evader_reduction k M hcard δ Δ hδ0 hδ hΔ R hR Bl hBlinj hBllazy hBllazy2
    have hEp : E.pos [] = x₁ := by
      apply hmiss
      rw [hBl0, hB'0] at hEpos
      exact hEpos
    set W : ℝ := ∑ j, p j * evaderOfflineCost x₁ (σ j) with hWdef
    have hWN : Cst / d + 1 ≤ W := hOPT x₁
    -- chain of estimates
    have h1 : c₀ * Real.log k ^ 2 * W ≤ ∑ j, p j * E.cost (σ j) := by
      have := hLB E
      rw [hEp] at this
      exact this
    have h3 : ∑ j, p j * E.cost (σ j) ≤ 4 * ∑ j, p j * Bl.cost (τ j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have := hEcost (σ j)
      have hpj := hp0 j
      nlinarith [this, hpj]
    have h5 : ∑ j, p j * Bl.cost (τ j) ≤ (∑ j, p j * B.cost (τ j)) + K := by
      have step : ∀ j, Bl.cost (τ j) ≤ B.cost (τ j) + K := by
        intro j
        refine le_trans (hBlcost (τ j)) ?_
        have := restart_cost_le' B C₁ (τ j)
        rw [hKdef, ← hi0]
        exact this
      have : ∑ j, p j * Bl.cost (τ j) ≤ ∑ j, p j * (B.cost (τ j) + K) := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left (step j) (hp0 j)
      calc ∑ j, p j * Bl.cost (τ j) ≤ ∑ j, p j * (B.cost (τ j) + K) := this
        _ = (∑ j, p j * B.cost (τ j)) + (∑ j, p j) * K := by
            rw [Finset.sum_mul, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = (∑ j, p j * B.cost (τ j)) + K := by rw [hp1]; ring
    have h7 : ∀ j, offlineCost C₀ (τ j) ≤ evaderOfflineCost x₁ (σ j) + K' := by
      intro j
      refine le_trans (offlineCost_shift' hk1 C₀ C₁ (τ j)) ?_
      have := evader_to_server_offline k hk1 M hcard R C₁ hC₁inj x₁ hx₁ (σ j) (hSne j)
      rw [hτdef]
      simp only
      linarith [this]
    have h8 : ∑ j, p j * offlineCost C₀ (τ j) ≤ W + K' := by
      have : ∑ j, p j * offlineCost C₀ (τ j)
          ≤ ∑ j, p j * (evaderOfflineCost x₁ (σ j) + K') :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h7 j) (hp0 j)
      calc ∑ j, p j * offlineCost C₀ (τ j)
          ≤ ∑ j, p j * (evaderOfflineCost x₁ (σ j) + K') := this
        _ = (∑ j, p j * evaderOfflineCost x₁ (σ j)) + (∑ j, p j) * K' := by
            rw [Finset.sum_mul, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = W + K' := by rw [hp1, hWdef]; ring
    -- combine
    have hfinal : c₀ * Real.log k ^ 2 * W ≤ 4 * r * W + Cst := by
      have hstep : ∑ j, p j * B.cost (τ j)
          ≤ r * (∑ j, p j * offlineCost C₀ (τ j)) + a + 1 := hi
      have hmul : r * (∑ j, p j * offlineCost C₀ (τ j)) ≤ r * (W + K') :=
        mul_le_mul_of_nonneg_left h8 hr
      rw [hCstdef]
      nlinarith [h1, h3, h5, hstep, hmul]
    have : d * W ≤ Cst := by rw [hddef]; nlinarith [hfinal]
    have hlow : Cst + d ≤ d * W := by
      have : d * (Cst / d + 1) ≤ d * W := mul_le_mul_of_nonneg_left hWN (le_of_lt hd)
      have heq : d * (Cst / d + 1) = Cst + d := by
        field_simp
      linarith [this, heq.symm.le, heq.le]
    linarith
  -- remove the sign assumption on ρ
  have hmono : A.IsCompetitiveFrom C₀ (max ρ 0) := by
    obtain ⟨hstart, a, hA⟩ := hcomp
    refine ⟨hstart, a, fun σ => le_trans (hA σ) ?_⟩
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 ≤ offlineCost C₀ σ := offlineCost_nonneg' hk1 C₀ σ
    have : ρ * offlineCost C₀ σ ≤ max ρ 0 * offlineCost C₀ σ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    linarith
  have hkey := core (max ρ 0) (le_max_right _ _) hmono
  have hmaxpos : 0 < max ρ 0 := by nlinarith [hkey, hpos]
  have : max ρ 0 = ρ := by
    rcases max_cases ρ 0 with ⟨h, _⟩ | ⟨h, h2⟩
    · exact h
    · exfalso; rw [h] at hmaxpos; exact lt_irrefl 0 hmaxpos
  rw [this] at hkey
  linarith

end KServer

open KServer in
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ m : MetricSpace (Fin (k + 1)),
        ∀ (C₀ : Config k (Fin (k + 1)))
          (A : @RandomizedAlgorithm k (Fin (k + 1)) m) (ρ : ℝ),
          @RandomizedAlgorithm.IsCompetitiveFrom k (Fin (k + 1)) m A C₀ ρ →
            c * Real.log k ^ 2 ≤ ρ := by
  obtain ⟨c₀, hc₀, k₀, hMSS⟩ := mss_randomized_lower_bound
  refine ⟨c₀ / 4, by positivity, max k₀ 2, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := hMSS k (le_trans (le_max_left _ _) hk)
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hk
  refine ⟨m, ?_⟩
  intro C₀ A ρ hcomp
  exact @kserver_of_mss k hk2 (Fin (k + 1)) m _ (Fintype.card_fin _) c₀ hc₀ hm C₀ A ρ hcomp
