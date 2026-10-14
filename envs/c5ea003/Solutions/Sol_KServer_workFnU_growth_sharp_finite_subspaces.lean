-- Prove2me | solution 1 for KServer.workFnU_growth_sharp_finite_subspaces
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T23:15:27.623137+00:00
-- url     : https://prove2.me/submissions/0df04040-4041-4198-9686-1d14cc7fe03e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KServer_workFnU_initial_stability
import Theorems.Thm_KServer_workFnU_coalesced_reset
import Theorems.Thm_KServer_workFnU_growth_sharp_coalesced_finite
import Theorems.Thm_KServer_workFnU_isometry_embedding
import Theorems.Thm_KServer_workFnU_mono
import Theorems.Thm_KServer_workFnU_step_le
import Theorems.Thm_KServer_workFnU_resolves
import Theorems.Thm_KServer_workFn_approx_offlineCost
import Theorems.Thm_KServer_offlineCost_le_workFn

set_option autoImplicit false
open KServer

private lemma move_nonneg {k : ℕ} {M : Type} [MetricSpace M]
    (C D : Config k M) : 0 ≤ moveCost C D :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

private lemma offline_nonneg {k : ℕ} {M : Type} [MetricSpace M]
    (C : Config k M) (σ : List M) : 0 ≤ offlineCost C σ := by
  apply Real.sInf_nonneg
  rintro v ⟨S, hS, rfl⟩
  exact Finset.sum_nonneg fun _ _ => move_nonneg _ _

private lemma exists_schedule (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C : Config k M) (σ : List M) : ∃ S, ServesFrom C σ S := by
  let S : ℕ → Config k M := fun t i => if t = 0 then C i else σ[t - 1]?.getD (C i)
  refine ⟨S, ?_, ?_⟩
  · funext i
    simp [S]
  · intro j
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp [S, List.get_eq_getElem]

private lemma offline_map_le (k : ℕ) (hk : 1 ≤ k) (M N : Type)
    [MetricSpace M] [MetricSpace N] (e : M → N)
    (he : ∀ x y, dist (e x) (e y) = dist x y)
    (C : Config k M) (σ : List M) :
    offlineCost (fun i => e (C i)) (σ.map e) ≤ offlineCost C σ := by
  obtain ⟨S₀, hS₀⟩ := exists_schedule k hk M C σ
  apply le_csInf
  · exact ⟨_, S₀, hS₀, rfl⟩
  · rintro v ⟨S, hS, rfl⟩
    let T : ℕ → Config k N := fun t i => e (S t i)
    have hT : ServesFrom (fun i => e (C i)) (σ.map e) T := by
      constructor
      · simp only [T, hS.1]
      · intro j
        have hj : j.val < σ.length := by simpa using j.isLt
        obtain ⟨i, hi⟩ := hS.2 ⟨j.val, hj⟩
        refine ⟨i, ?_⟩
        simpa [T, List.get_eq_getElem] using congrArg e hi
    have hbelow : BddBelow {c : ℝ | ∃ S : ℕ → Config k N,
        ServesFrom (fun i => e (C i)) (σ.map e) S ∧
        c = ∑ j ∈ Finset.range (σ.map e).length, moveCost (S j) (S (j + 1))} := by
      refine ⟨0, ?_⟩
      rintro v ⟨S, _, rfl⟩
      exact Finset.sum_nonneg fun _ _ => move_nonneg _ _
    have hh := csInf_le hbelow ⟨T, hT, rfl⟩
    simpa [offlineCost, T, moveCost, he] using hh

private lemma u_rec_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C : Config k M) (σ : List M) (r : M) (X : Config k M) (i : Fin k) :
    workFnU C (σ ++ [r]) X ≤ workFnU C σ (Function.update X i r) + dist r (X i) := by
  classical
  have hh := workFnU_step_le k hk M C σ r X (Function.update X i r) ⟨i, by simp⟩
  have hm : moveCost (Function.update X i r) X = dist r (X i) := by
    unfold moveCost
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [Function.update_of_ne hji]
    · simp
  simpa only [hm] using hh

private lemma u_rec_ge (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C : Config k M) (σ : List M) (r : M) (X : Config k M) :
    ∃ i : Fin k, workFnU C σ (Function.update X i r) + dist r (X i) ≤
      workFnU C (σ ++ [r]) X := by
  classical
  obtain ⟨i, hi⟩ := workFnU_resolves k hk M C σ r X
  refine ⟨i, ?_⟩
  rw [hi]
  have hm := workFnU_mono k hk M C σ r (Function.update X i r)
  linarith

private lemma profile_transport (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (A B : Config k M) (ρ : List M) (D : ℝ)
    (hbase : ∀ X : Config k M, workFnU A ρ X = D + workFnU B [] X)
    (τ : List M) :
    (∀ X : Config k M, workFnU A (ρ ++ τ) X = D + workFnU B τ X) ∧
      offlineCost A (ρ ++ τ) = D + offlineCost B τ := by
  classical
  have hwork (σ : List M) (X : Config k M) :
      workFnU A (ρ ++ σ) X = D + workFnU B σ X := by
    induction σ using List.reverseRecOn generalizing X with
    | nil => simpa using hbase X
    | @append_singleton σ r ih =>
      rw [← List.append_assoc]
      apply le_antisymm
      · obtain ⟨i, hi⟩ := u_rec_ge k hk M B σ r X
        have hh := u_rec_le k hk M A (ρ ++ σ) r X i
        rw [ih] at hh
        linarith
      · obtain ⟨i, hi⟩ := u_rec_ge k hk M A (ρ ++ σ) r X
        have hh := u_rec_le k hk M B σ r X i
        rw [ih] at hi
        linarith
  have hlo (C : Config k M) (σ : List M) (X : Config k M) : offlineCost C σ ≤ workFnU C σ X := by
    unfold workFnU
    exact le_ciInf fun π => offlineCost_le_workFn k hk M C σ (X ∘ π)
  have happ (C : Config k M) (σ : List M) (ε : ℝ) (hε : 0 < ε) :
      ∃ X : Config k M, workFnU C σ X ≤ offlineCost C σ + ε := by
    obtain ⟨X, hX⟩ := workFn_approx_offlineCost k hk M C σ ε hε
    refine ⟨X, le_trans ?_ hX⟩
    simpa [workFnU] using
      (ciInf_le (Finite.bddBelow_range (fun π : Equiv.Perm (Fin k) => workFn C σ (X ∘ π))) (Equiv.refl _))
  refine ⟨hwork τ, le_antisymm ?_ ?_⟩
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨X, hX⟩ := happ B τ ε hε
    have hh := hlo A (ρ ++ τ) X
    rw [hwork] at hh
    linarith
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨X, hX⟩ := happ A (ρ ++ τ) ε hε
    rw [hwork] at hX
    have hh := hlo B τ X
    linarith

private lemma injective_growth (k : ℕ) (hk : 3 ≤ k) (M : Type)
    [MetricSpace M] [Fintype M] (B : Config k M) (hB : Function.Injective B)
    (p : M) (τ : List M) :
    ∃ u : ℕ → ℝ,
      (∀ t, t < τ.length → ∀ Y : Config k M, Function.Injective Y →
        workFnU B (τ.take (t + 1)) Y ≤ workFnU B (τ.take t) Y + u t) ∧
      (∑ t ∈ Finset.range τ.length, u t) ≤
        ((k : ℝ) + 1) * offlineCost B τ + ((k : ℝ) + 1) * ∑ i, dist p (B i) := by
  classical
  have hk1 : 1 ≤ k := by omega
  obtain ⟨ρ, hbase⟩ := workFnU_coalesced_reset k hk1 M B hB p
  have hρ (τ : List M) := profile_transport k hk1 M (fun _ => p) B ρ _ hbase τ
  obtain ⟨v, hv, hsum⟩ := workFnU_growth_sharp_coalesced_finite k hk M p (ρ ++ τ)
  have htake (t : ℕ) : (ρ ++ τ).take (ρ.length + t) = ρ ++ τ.take t := by
    rw [List.take_append, Nat.add_sub_cancel_left, List.take_of_length_le (by omega)]
  have htail (t : ℕ) (ht : t < τ.length) (Y : Config k M) (hY : Function.Injective Y) :
      workFnU B (τ.take (t + 1)) Y ≤ workFnU B (τ.take t) Y + v (ρ.length + t) := by
    have hh := hv (ρ.length + t) (by simp only [List.length_append]; omega) Y hY
    rw [show ρ.length + t + 1 = ρ.length + (t + 1) by omega, htake, htake,
      (hρ _).1 Y, (hρ _).1 Y] at hh
    linarith
  have hv0 (t : ℕ) (ht : t < ρ.length) : 0 ≤ v t := by
    have ht' : t < (ρ ++ τ).length := by simp only [List.length_append]; omega
    have hh := hv t ht' B hB
    have hstep : (ρ ++ τ).take (t + 1) = (ρ ++ τ).take t ++ [(ρ ++ τ)[t]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem ht']
      rfl
    have hm := workFnU_mono k hk1 M (fun _ => p) ((ρ ++ τ).take t) ((ρ ++ τ)[t]) B
    rw [hstep] at hh
    linarith
  have hpref : 0 ≤ ∑ t ∈ Finset.range ρ.length, v t :=
    Finset.sum_nonneg fun t ht => hv0 t (Finset.mem_range.mp ht)
  rw [(hρ τ).2, List.length_append, Finset.sum_range_add] at hsum
  refine ⟨fun t => v (ρ.length + t), htail, ?_⟩
  have hh : (∑ t ∈ Finset.range τ.length, v (ρ.length + t)) =
      ∑ t ∈ Finset.range τ.length, v (t + ρ.length) := by
    congr 1
    funext t
    rw [Nat.add_comm]
  rw [hh]
  nlinarith

private lemma finite_lift (k : ℕ) (M : Type) [MetricSpace M] [Fintype M]
    (C : Config k M) (p : M) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : Finset (M × ℝ)) (e : M → Q) (B : Config k Q),
      (∀ x y, dist (e x) (e y) = dist x y) ∧ Function.Injective B ∧
      moveCost (fun i => e (C i)) B ≤ (k : ℝ)^2 * ε ∧
      (∑ i, dist (e p) (B i)) ≤ (∑ i, dist p (C i)) + (k : ℝ)^2 * ε := by
  classical
  let Q : Finset (M × ℝ) := Finset.univ.biUnion fun x : M =>
    (Finset.range (k + 1)).image (fun j : ℕ => (x, ε * (j : ℝ)))
  have hmem (x : M) (j : ℕ) (hj : j ≤ k) : (x, ε * (j : ℝ)) ∈ Q := by
    exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩⟩
  let e : M → Q := fun x => ⟨(x, 0), by simpa using hmem x 0 (by omega)⟩
  let B : Config k Q := fun i => ⟨(C i, ε * ((i.val + 1 : ℕ) : ℝ)),
    hmem _ _ (by omega)⟩
  have he (x y : M) : dist (e x) (e y) = dist x y := by
    simp [e, Subtype.dist_eq, Prod.dist_eq]
  have hB : Function.Injective B := by
    intro i j hij
    have hh := congrArg (fun z : Q => z.val.2) hij
    dsimp only [B] at hh
    have hc : ((i.val + 1 : ℕ) : ℝ) = ((j.val + 1 : ℕ) : ℝ) :=
      (mul_left_cancel₀ (ne_of_gt hε)) hh
    exact Fin.ext (by exact_mod_cast (show (i.val : ℝ) = (j.val : ℝ) by push_cast at hc; linarith))
  have hheight (i : Fin k) : 0 ≤ ε * ((i.val + 1 : ℕ) : ℝ) ∧
      ε * ((i.val + 1 : ℕ) : ℝ) ≤ (k : ℝ) * ε := by
    constructor
    · positivity
    · have hi : ((i.val + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show i.val + 1 ≤ k by omega)
      nlinarith
  have hd (x : M) (i : Fin k) :
      dist (e x) (B i) = max (dist x (C i)) (ε * ((i.val + 1 : ℕ) : ℝ)) := by
    change dist ((x, (0 : ℝ))) (C i, ε * ((i.val + 1 : ℕ) : ℝ)) = _
    rw [Prod.dist_eq]
    simp only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hheight i).1]
  have hmove : moveCost (fun i => e (C i)) B ≤ (k : ℝ)^2 * ε := by
    calc
      moveCost (fun i => e (C i)) B ≤ ∑ _ : Fin k, (k : ℝ) * ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [hd, dist_self, max_eq_right (hheight i).1]
        exact (hheight i).2
      _ = (k : ℝ)^2 * ε := by simp; ring
  have hspread : (∑ i, dist (e p) (B i)) ≤ (∑ i, dist p (C i)) + (k : ℝ)^2 * ε := by
    calc
      (∑ i, dist (e p) (B i)) ≤ ∑ i, (dist p (C i) + (k : ℝ) * ε) := by
        apply Finset.sum_le_sum
        intro i _
        rw [hd]
        apply max_le
        · have hk0 : 0 ≤ (k : ℝ) * ε := by positivity
          linarith
        · have hd0 : 0 ≤ dist p (C i) := dist_nonneg
          linarith [(hheight i).2]
      _ = _ := by rw [Finset.sum_add_distrib]; simp; ring
  exact ⟨Q, e, B, he, hB, hmove, hspread⟩

private lemma finite_growth (k : ℕ) (hk : 3 ≤ k) (M : Type)
    [MetricSpace M] [Fintype M] (C : Config k M) (p : M) (τ : List M) :
    ∃ u : ℕ → ℝ,
      (∀ t, t < τ.length → ∀ Y : Config k M, Function.Injective Y →
        workFnU C (τ.take (t + 1)) Y ≤ workFnU C (τ.take t) Y + u t) ∧
      (∑ t ∈ Finset.range τ.length, u t) ≤
        ((k : ℝ) + 1) * offlineCost C τ + ((k : ℝ) + 1) * ∑ i, dist p (C i) := by
  classical
  have hk1 : 1 ≤ k := by omega
  have ha : 0 ≤ (k : ℝ) + 1 := by positivity
  by_cases hex : ∃ Y : Config k M, Function.Injective Y
  · let I := {Y : Config k M // Function.Injective Y}
    letI : Nonempty I := ⟨⟨hex.choose, hex.choose_spec⟩⟩
    let f (t : ℕ) (Y : I) := workFnU C (τ.take (t + 1)) Y.val - workFnU C (τ.take t) Y.val
    have hmax (t : ℕ) : ∃ X : I, ∀ Y : I, f t Y ≤ f t X := Finite.exists_max (f t)
    choose X hX using hmax
    refine ⟨fun t => f t (X t), ?_, ?_⟩
    · intro t ht Y hY
      have hh := hX t (⟨Y, hY⟩ : I)
      dsimp only [f] at hh ⊢
      linarith
    · let R : ℝ := (k : ℝ)^2 * (2 * (τ.length : ℝ) + 2 * ((k : ℝ) + 1))
      have hR : 0 ≤ R := by dsimp [R]; positivity
      have hpert (ε : ℝ) (hε : 0 < ε) :
          (∑ t ∈ Finset.range τ.length, f t (X t)) ≤
            ((k : ℝ) + 1) * offlineCost C τ + ((k : ℝ) + 1) * ∑ i, dist p (C i) + ε * R := by
        obtain ⟨Q, e, B, he, hB, hmove, hspread⟩ := finite_lift k M C p ε hε
        have heinj : Function.Injective e := by
          intro x y hxy
          apply dist_eq_zero.mp
          rw [← he x y, hxy, dist_self]
        obtain ⟨v, hv, hsum⟩ := injective_growth k hk Q B hB (e p) (τ.map e)
        let A : Config k Q := fun i => e (C i)
        have hoff : offlineCost B (τ.map e) ≤ offlineCost C τ + (k : ℝ)^2 * ε := by
          have hh := (abs_le.mp (workFnU_initial_stability k hk1 Q A B (τ.map e)).2).1
          have hm := offline_map_le k hk1 M Q e he C τ
          dsimp only [A] at hh
          linarith
        have htbound (t : ℕ) (ht : t < τ.length) : f t (X t) ≤ v t + 2 * (k : ℝ)^2 * ε := by
          let Y : Config k Q := fun i => e ((X t).val i)
          have hY : Function.Injective Y := heinj.comp (X t).property
          have hh := hv t (by simpa using ht) Y hY
          have hw (n : ℕ) : workFnU A ((τ.map e).take n) Y = workFnU C (τ.take n) (X t).val := by
            rw [← List.map_take]
            exact workFnU_isometry_embedding k hk1 M Q e he C (τ.take n) (X t).val
          have h1 := abs_le.mp ((workFnU_initial_stability k hk1 Q A B ((τ.map e).take (t + 1))).1 Y)
          have h0 := abs_le.mp ((workFnU_initial_stability k hk1 Q A B ((τ.map e).take t)).1 Y)
          rw [hw] at h1 h0
          dsimp only [f]
          dsimp only [A] at h1 h0
          linarith
        have hs : (∑ t ∈ Finset.range τ.length, f t (X t)) ≤
            (∑ t ∈ Finset.range τ.length, v t) + 2 * (τ.length : ℝ) * (k : ℝ)^2 * ε := by
          calc
            (∑ t ∈ Finset.range τ.length, f t (X t)) ≤
                ∑ t ∈ Finset.range τ.length, (v t + 2 * (k : ℝ)^2 * ε) :=
              Finset.sum_le_sum fun t ht => htbound t (Finset.mem_range.mp ht)
            _ = _ := by rw [Finset.sum_add_distrib]; simp; ring
        simp only [List.length_map] at hsum
        have hO := mul_le_mul_of_nonneg_left hoff ha
        have hD := mul_le_mul_of_nonneg_left hspread ha
        dsimp only [R]
        nlinarith
      apply le_of_forall_pos_le_add
      intro δ hδ
      have hden : 0 < R + 1 := by linarith
      have hε : 0 < δ / (R + 1) := div_pos hδ hden
      have hh := hpert (δ / (R + 1)) hε
      have heq : δ / (R + 1) * (R + 1) = δ := div_mul_cancel₀ _ (ne_of_gt hden)
      nlinarith
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · intro t ht Y hY
      exact False.elim (hex ⟨Y, hY⟩)
    · have hO := mul_nonneg ha (offline_nonneg C τ)
      have hD : 0 ≤ ((k : ℝ) + 1) * ∑ i, dist p (C i) :=
        mul_nonneg ha (Finset.sum_nonneg fun _ _ => dist_nonneg)
      simpa using add_nonneg hO hD

theorem solution (k : ℕ) (hk : 3 ≤ k) (M : Type) [MetricSpace M] (C₀ : Config k M)
    (hM : ∃ f : Fin (k + 3) → M, Function.Injective f) :
    ∃ c : ℝ, ∀ (P : Finset M) (D₀ : Config k P),
      (∀ i, (D₀ i : M) = C₀ i) → ∀ τ : List P, ∃ u : ℕ → ℝ,
        (∀ t, t < τ.length → ∀ Y : Config k P, Function.Injective Y →
          workFnU D₀ (τ.take (t + 1)) Y ≤ workFnU D₀ (τ.take t) Y + u t) ∧
        (∑ t ∈ Finset.range τ.length, u t) ≤ ((k : ℝ) + 1) * offlineCost D₀ τ + c := by
  let i₀ : Fin k := ⟨0, by omega⟩
  refine ⟨((k : ℝ) + 1) * ∑ i, dist (C₀ i₀) (C₀ i), ?_⟩
  intro P D₀ hD τ
  obtain ⟨u, hu, hsum⟩ := finite_growth k hk P D₀ (D₀ i₀) τ
  refine ⟨u, hu, ?_⟩
  have hdist (i : Fin k) : dist (D₀ i₀) (D₀ i) = dist (C₀ i₀) (C₀ i) := by
    change dist (D₀ i₀ : M) (D₀ i : M) = _
    rw [hD, hD]
  simpa only [hdist] using hsum

#print axioms solution
