-- Prove2me | solution 1 for MetricTSP.tour_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T19:56:42.78802+00:00
-- url     : https://prove2.me/submissions/aba1b824-6f4e-4886-9eb4-28d201226f3e

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_graph_cost

namespace MetricTSP

open Finset Equiv Equiv.Perm

variable {n : ℕ}

lemma metric_nonneg' {c : Fin n → Fin n → ℝ} (hc : IsMetricCost c) (u v : Fin n) :
    0 ≤ c u v := by
  obtain ⟨hsym, hdiag, htri⟩ := hc
  have h := htri u v u
  rw [hdiag u, hsym v u] at h
  linarith

lemma pairCost_nonneg {c : Fin n → Fin n → ℝ} (hc0 : ∀ u v, 0 ≤ c u v)
    (e : Sym2 (Fin n)) : 0 ≤ pairCost c e := by
  induction e with
  | _ u v =>
    show (0 : ℝ) ≤ (c u v + c v u) / 2
    have h1 := hc0 u v
    have h2 := hc0 v u
    linarith

lemma pairCost_mk {c : Fin n → Fin n → ℝ} (hsym : ∀ u v, c u v = c v u) (u v : Fin n) :
    pairCost c s(u, v) = c u v := by
  show (c u v + c v u) / 2 = c u v
  rw [hsym v u]
  ring

/-- The cost of a permutation viewed as a set of directed steps `v → σ v`.
For a cyclic permutation this is the cost of the corresponding tour; fixed
points contribute the diagonal cost `c v v = 0` of a metric. -/
noncomputable def permCost (c : Fin n → Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ v, c v (σ v)

lemma permCost_one {c : Fin n → Fin n → ℝ} (hdiag : ∀ v, c v v = 0) :
    permCost c (1 : Equiv.Perm (Fin n)) = 0 := by
  unfold permCost
  simp [hdiag]

/-- Inserting a new city `w` right after `p` in the cyclic order: the cost
increases by at most `2 c(p, w)`, by the triangle inequality. -/
lemma permCost_insert {c : Fin n → Fin n → ℝ} (hc : IsMetricCost c)
    (σ : Equiv.Perm (Fin n)) (p w : Fin n) (hpw : p ≠ w) (hw : σ w = w) :
    permCost c (σ * Equiv.swap p w) ≤ permCost c σ + 2 * c p w := by
  obtain ⟨hsym, hdiag, htri⟩ := hc
  have hval : ∀ v, v ≠ p → v ≠ w → (σ * Equiv.swap p w) v = σ v := by
    intro v hvp hvw
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hvp hvw]
  have hp' : (σ * Equiv.swap p w) p = w := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hw]
  have hw' : (σ * Equiv.swap p w) w = σ p := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have hsplit : ∀ τ : Equiv.Perm (Fin n), permCost c τ
      = c p (τ p) + c w (τ w) + ∑ v ∈ (univ.erase p).erase w, c v (τ v) := by
    intro τ
    unfold permCost
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    rw [← Finset.add_sum_erase _ (fun v => c v (τ v))
      (Finset.mem_erase.mpr ⟨fun h => hpw h.symm, Finset.mem_univ w⟩)]
    ring
  rw [hsplit (σ * Equiv.swap p w), hsplit σ]
  have hrest : ∑ v ∈ (univ.erase p).erase w, c v ((σ * Equiv.swap p w) v)
      = ∑ v ∈ (univ.erase p).erase w, c v (σ v) := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.mem_erase] at hv
    have hv2 := Finset.mem_erase.mp hv.2
    rw [hval v hv2.1 hv.1]
  rw [hrest, hp', hw', hw, hdiag w]
  have htriangle : c w (σ p) ≤ c w p + c p (σ p) := htri w p (σ p)
  have hs : c w p = c p w := hsym w p
  linarith

/-- Extending a cycle by one new point: multiplying on the right by the
transposition `(p w)`, where `p` is on the cycle and `w` is a fixed point,
yields a cycle whose support gains exactly `w`. -/
lemma cycle_extend {σ : Equiv.Perm (Fin n)} (hσ : σ.IsCycle) (p w : Fin n)
    (hp : p ∈ σ.support) (hw : w ∉ σ.support) :
    (σ * Equiv.swap p w).IsCycle ∧ (σ * Equiv.swap p w).support = insert w σ.support := by
  classical
  have hpw : p ≠ w := fun h => hw (h ▸ hp)
  have hwfix : σ w = w := Equiv.Perm.notMem_support.mp hw
  set τ := σ * Equiv.swap p w with hτ
  have hτp : τ p = w := by
    rw [hτ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, hwfix]
  have hτw : τ w = σ p := by
    rw [hτ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have hτother : ∀ v, v ≠ p → v ≠ w → τ v = σ v := by
    intro v hvp hvw
    rw [hτ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hvp hvw]
  have hσp : σ p ≠ p := Equiv.Perm.mem_support.mp hp
  have hσpw : σ p ≠ w := by
    intro h
    exact hw (h ▸ Equiv.Perm.apply_mem_support.mpr hp)
  have hsupp : τ.support = insert w σ.support := by
    ext v
    rw [Equiv.Perm.mem_support, Finset.mem_insert]
    by_cases hvp : v = p
    · subst hvp
      rw [hτp]
      constructor
      · intro _; right; exact hp
      · intro _; exact fun h => (hpw h.symm).elim
    · by_cases hvw : v = w
      · subst hvw
        rw [hτw]
        constructor
        · intro _; left; rfl
        · intro _; exact fun h => (hσpw h).elim
      · rw [hτother v hvp hvw]
        constructor
        · intro h
          right
          exact Equiv.Perm.mem_support.mpr h
        · intro h
          rcases h with h | h
          · exact absurd h.symm (fun hh => hvw hh.symm)
          · exact Equiv.Perm.mem_support.mp h
  refine ⟨?_, hsupp⟩
  have hτwne : τ w ≠ w := by rw [hτw]; exact hσpw
  refine ⟨w, hτwne, ?_⟩
  intro y hy
  have hymem : y ∈ τ.support := Equiv.Perm.mem_support.mpr hy
  rw [hsupp, Finset.mem_insert] at hymem
  have hpw_cyc : τ.SameCycle p w := ⟨1, by simpa using hτp⟩
  rcases hymem with rfl | hyS
  · exact Equiv.Perm.SameCycle.refl τ y
  · have hyp : σ.SameCycle y p := hσ.sameCycle (Equiv.Perm.mem_support.mp hyS)
      (Equiv.Perm.mem_support.mp hp)
    obtain ⟨k, _, hσk⟩ := hyp.exists_pow_eq'
    have hex : ∃ m : ℕ, (σ ^ m) y = p := ⟨k, hσk⟩
    let m := Nat.find hex
    have hm : (σ ^ m) y = p := Nat.find_spec hex
    have hmin : ∀ j < m, (σ ^ j) y ≠ p := fun j hj => Nat.find_min hex hj
    have hagree : ∀ j ≤ m, (τ ^ j) y = (σ ^ j) y := by
      intro j hj
      induction j with
      | zero => simp
      | succ i ih =>
          have hi : i ≤ m := by omega
          have hival : (σ ^ i) y ≠ p := hmin i (by omega)
          have hiw : (σ ^ i) y ≠ w := by
            intro h
            apply hw
            rw [← h]
            exact Equiv.Perm.pow_apply_mem_support.mpr hyS
          rw [pow_succ', Equiv.Perm.mul_apply, ih hi, hτother _ hival hiw,
            ← Equiv.Perm.mul_apply, ← pow_succ']
    have hyτp : τ.SameCycle y p := by
      refine ⟨(m : ℤ), ?_⟩
      rw [zpow_natCast, hagree m le_rfl]
      exact hm
    exact (hyτp.trans hpw_cyc).symm

open Classical in
/-- The cost of the edges of `G` inside a set `S` of cities. -/
noncomputable def graphCostWithin (c : Fin n → Fin n → ℝ) (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℝ :=
  ∑ e ∈ G.edgeSet.toFinset.filter (fun e => ∀ v ∈ e, v ∈ S), pairCost c e

lemma graphCostWithin_le (c : Fin n → Fin n → ℝ) (hc0 : ∀ u v, 0 ≤ c u v)
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    graphCostWithin c G S ≤ graphCost c G := by
  classical
  unfold graphCostWithin graphCost
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro e _ _
  exact pairCost_nonneg hc0 e

lemma graphCostWithin_nonneg (c : Fin n → Fin n → ℝ) (hc0 : ∀ u v, 0 ≤ c u v)
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    0 ≤ graphCostWithin c G S := by
  classical
  unfold graphCostWithin
  apply Finset.sum_nonneg
  intro e _
  exact pairCost_nonneg hc0 e

lemma graphCostWithin_insert (c : Fin n → Fin n → ℝ) (hc0 : ∀ u v, 0 ≤ c u v)
    (hsym : ∀ u v, c u v = c v u)
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (p w : Fin n)
    (hadj : G.Adj p w) (hpS : p ∈ S) (hwS : w ∉ S) :
    graphCostWithin c G S + c p w ≤ graphCostWithin c G (insert w S) := by
  classical
  unfold graphCostWithin
  have he0 : s(p, w) ∈ G.edgeSet.toFinset := by
    rw [Set.mem_toFinset]
    exact hadj
  have he0S : s(p, w) ∉ G.edgeSet.toFinset.filter (fun e => ∀ v ∈ e, v ∈ S) := by
    intro hmem
    rw [Finset.mem_filter] at hmem
    exact hwS (hmem.2 w (Sym2.mem_mk_right p w))
  have hsub : insert s(p, w) (G.edgeSet.toFinset.filter (fun e => ∀ v ∈ e, v ∈ S))
      ⊆ G.edgeSet.toFinset.filter (fun e => ∀ v ∈ e, v ∈ insert w S) := by
    intro e he
    rw [Finset.mem_insert] at he
    rcases he with rfl | he
    · rw [Finset.mem_filter]
      refine ⟨he0, ?_⟩
      intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact Finset.mem_insert_of_mem hpS
      · exact Finset.mem_insert_self _ _
    · rw [Finset.mem_filter] at he ⊢
      exact ⟨he.1, fun v hv => Finset.mem_insert_of_mem (he.2 v hv)⟩
  calc (∑ e ∈ G.edgeSet.toFinset.filter (fun e => ∀ v ∈ e, v ∈ S), pairCost c e) + c p w
      = ∑ e ∈ insert s(p, w) (G.edgeSet.toFinset.filter (fun e => ∀ v ∈ e, v ∈ S)),
          pairCost c e := by
        rw [Finset.sum_insert he0S, pairCost_mk hsym]
        ring
    _ ≤ ∑ e ∈ G.edgeSet.toFinset.filter (fun e => ∀ v ∈ e, v ∈ insert w S),
          pairCost c e := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro e _ _
        exact pairCost_nonneg hc0 e

/-- Prim-style growth: starting from a single city, repeatedly insert a city
adjacent (in `G`) to the visited set, right after its attachment point in the
cyclic order. Each insertion pays at most twice the connecting edge. -/
lemma grow (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (G : SimpleGraph (Fin n)) (hG : G.Connected) (v0 : Fin n) :
    ∀ k (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)),
      ((σ = 1 ∧ S = {v0}) ∨ (σ.IsCycle ∧ σ.support = S)) →
      (univ \ S).card = k →
      permCost c σ ≤ 2 * graphCostWithin c G S →
      ∃ σ' : Equiv.Perm (Fin n),
        ((σ' = 1 ∧ ({v0} : Finset (Fin n)) = univ) ∨ (σ'.IsCycle ∧ σ'.support = univ)) ∧
        permCost c σ' ≤ 2 * graphCost c G := by
  classical
  have hc0 := metric_nonneg' hc
  intro k
  induction k with
  | zero =>
      intro σ S hinv hcard hcost
      have huniv : S = univ := by
        have h0 : univ \ S = ∅ := Finset.card_eq_zero.mp hcard
        apply Finset.Subset.antisymm (Finset.subset_univ S)
        intro a _
        by_contra ha
        have : a ∈ univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩
        rw [h0] at this
        exact Finset.notMem_empty a this
      refine ⟨σ, ?_, le_trans hcost ?_⟩
      · rcases hinv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨h1, h2 ▸ huniv⟩
        · right; exact ⟨h1, h2.trans huniv⟩
      · have := graphCostWithin_le c hc0 G S
        linarith
  | succ k ih =>
      intro σ S hinv hcard hcost
      have hSne : S.Nonempty := by
        rcases hinv with ⟨_, rfl⟩ | ⟨hcyc, rfl⟩
        · exact ⟨v0, Finset.mem_singleton_self v0⟩
        · obtain ⟨x, hx, _⟩ := hcyc
          exact ⟨x, Equiv.Perm.mem_support.mpr hx⟩
      obtain ⟨u, hu⟩ := hSne
      have hmiss : (univ \ S).Nonempty := by
        rw [← Finset.card_pos, hcard]
        omega
      obtain ⟨w', hw'⟩ := hmiss
      rw [Finset.mem_sdiff] at hw'
      obtain ⟨W⟩ := hG.preconnected u w'
      obtain ⟨d, _, hdS, hdS'⟩ := W.exists_boundary_dart (↑S : Set (Fin n))
        (by simpa using hu) (by simpa using hw'.2)
      have hpS : d.fst ∈ S := by simpa using hdS
      have hwS : d.snd ∉ S := by simpa using hdS'
      set p := d.fst with hpdef
      set w := d.snd with hwdef
      have hpw : p ≠ w := fun h => hwS (h ▸ hpS)
      have hwfix : σ w = w := by
        rcases hinv with ⟨h1, _⟩ | ⟨_, hsupp⟩
        · rw [h1]; rfl
        · exact Equiv.Perm.notMem_support.mp (fun hmem => hwS (hsupp ▸ hmem))
      have hinv' : ((σ * Equiv.swap p w) = 1 ∧ insert w S = {v0})
          ∨ ((σ * Equiv.swap p w).IsCycle ∧ (σ * Equiv.swap p w).support = insert w S) := by
        right
        rcases hinv with ⟨h1, hS⟩ | ⟨hcyc, hsupp⟩
        · have hpv : p = v0 := by
            rw [hS] at hpS
            simpa using hpS
          constructor
          · rw [h1, one_mul]
            exact Equiv.Perm.isCycle_swap hpw
          · rw [h1, one_mul, Equiv.Perm.support_swap hpw, hS, hpv]
            ext a
            simp only [Finset.mem_insert, Finset.mem_singleton]
            tauto
        · have hext := cycle_extend hcyc p w (hsupp ▸ hpS)
            (fun hmem => hwS (hsupp ▸ hmem))
          exact ⟨hext.1, hext.2.trans (by rw [hsupp])⟩
      have hcost' : permCost c (σ * Equiv.swap p w)
          ≤ 2 * graphCostWithin c G (insert w S) := by
        have h1 := permCost_insert hc σ p w hpw hwfix
        have h2 := graphCostWithin_insert c hc0 hc.1 G S p w d.adj hpS hwS
        linarith
      have hcard' : (univ \ insert w S).card = k := by
        have hwmem : w ∈ univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hwS⟩
        have hset : univ \ insert w S = (univ \ S).erase w := by
          ext a
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_univ,
            true_and]
          tauto
        rw [hset, Finset.card_erase_of_mem hwmem, hcard]
        omega
      exact ih (σ * Equiv.swap p w) (insert w S) hinv' hcard' hcost'

/-- The tour cost of an ordering `g` equals the step cost of the conjugated
rotation `g ∘ (·+1) ∘ g⁻¹`. -/
lemma tourCost_conj (c : Fin n → Fin n → ℝ) (g : Equiv.Perm (Fin n)) :
    tourCost c g = permCost c (g * (finRotate n) * g⁻¹) := by
  unfold tourCost permCost
  rw [← Equiv.sum_comp g (fun v => c v ((g * (finRotate n) * g⁻¹) v))]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  simp

lemma graphCost_nonneg (c : Fin n → Fin n → ℝ) (hc0 : ∀ u v, 0 ≤ c u v)
    (G : SimpleGraph (Fin n)) : 0 ≤ graphCost c G := by
  classical
  unfold graphCost
  apply Finset.sum_nonneg
  intro e _
  exact pairCost_nonneg hc0 e

/-- **Doubling a connected subgraph.** Any connected graph on `n ≥ 1` cities supports a
tour of cost at most twice its total edge cost. -/
theorem tour_of_connected_aux (n : ℕ) (hn : 1 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    ∃ π : Equiv.Perm (Fin n), tourCost c π ≤ 2 * graphCost c G := by
  classical
  have hc0 := metric_nonneg' hc
  set v0 : Fin n := ⟨0, by omega⟩ with hv0
  have hstart : permCost c (1 : Equiv.Perm (Fin n))
      ≤ 2 * graphCostWithin c G ({v0} : Finset (Fin n)) := by
    rw [permCost_one hc.2.1]
    have := graphCostWithin_nonneg c hc0 G ({v0} : Finset (Fin n))
    linarith
  obtain ⟨σ, hσinv, hσcost⟩ := grow c hc G hG v0 (univ \ ({v0} : Finset (Fin n))).card
    1 ({v0} : Finset (Fin n)) (Or.inl ⟨rfl, rfl⟩) rfl hstart
  have hg0 := graphCost_nonneg c hc0 G
  rcases hσinv with ⟨hσ1, huniv⟩ | ⟨hcyc, hsupp⟩
  · -- degenerate case: a single city
    have hn1 : n = 1 := by
      have h1 : ({v0} : Finset (Fin n)).card = (univ : Finset (Fin n)).card := by
        rw [huniv]
      simpa using h1.symm
    refine ⟨1, ?_⟩
    have htc : tourCost c 1 = 0 := by
      unfold tourCost
      apply Finset.sum_eq_zero
      intro i _
      have hri : finRotate n i = i := by
        subst hn1
        rw [finRotate_one]
        rfl
      rw [hri]
      simpa using hc.2.1 ((1 : Equiv.Perm (Fin n)) i)
    rw [htc]
    linarith
  · -- σ is a cycle with full support: conjugate the standard rotation onto it
    have hn2 : 2 ≤ n := by
      by_contra h
      have hn1 : n = 1 := by omega
      obtain ⟨x, hx, _⟩ := hcyc
      apply hx
      subst hn1
      exact Subsingleton.elim _ _
    have hconj : IsConj (finRotate n) σ := by
      rw [Equiv.Perm.isConj_iff_cycleType_eq, (isCycle_finRotate_of_le hn2).cycleType,
        support_finRotate_of_le hn2, hcyc.cycleType, hsupp]
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    refine ⟨g, ?_⟩
    rw [tourCost_conj c g, hg]
    exact hσcost

end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (hn : 1 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    ∃ π : Equiv.Perm (Fin n), tourCost c π ≤ 2 * graphCost c G :=
  MetricTSP.tour_of_connected_aux n hn c hc G hG

