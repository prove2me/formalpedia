-- Prove2me | solution 2 for rademacher_sampled_matrix_even_schatten_moment_trace_pairbound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T06:10:35.440522+00:00
-- url     : https://prove2.me/submissions/d345903c-9382-4e74-be03-7b21d31dea4a

import Mathlib
import Definitions.Def_matrix_completion_gram_schatten

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AF7

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- backward recursion over histories -/
noncomputable def Ex (κ : ℕ → (ℕ → V) → V → ℝ) : ℕ → ℕ → (ℕ → V) → ((ℕ → V) → ℝ) → ℝ
  | 0, _, h, F => F h
  | m+1, T, h, F => ∑ y, κ T h y * Ex κ m (T+1) (Function.update h (T+1) y) F

lemma Ex_zero (κ : ℕ → (ℕ → V) → V → ℝ) (T : ℕ) (h : ℕ → V) (F : (ℕ → V) → ℝ) :
    Ex κ 0 T h F = F h := rfl

lemma Ex_succ (κ : ℕ → (ℕ → V) → V → ℝ) (m T : ℕ) (h : ℕ → V) (F : (ℕ → V) → ℝ) :
    Ex κ (m+1) T h F = ∑ y, κ T h y * Ex κ m (T+1) (Function.update h (T+1) y) F := rfl

lemma Ex_mono (κ : ℕ → (ℕ → V) → V → ℝ) (hκ : ∀ T h y, 0 ≤ κ T h y) :
    ∀ m T (h : ℕ → V) (F G : (ℕ → V) → ℝ), (∀ h', F h' ≤ G h') → Ex κ m T h F ≤ Ex κ m T h G := by
  intro m
  induction m with
  | zero => intro T h F G hFG; exact hFG h
  | succ m ih =>
    intro T h F G hFG
    rw [Ex_succ, Ex_succ]
    apply Finset.sum_le_sum
    intro y _
    exact mul_le_mul_of_nonneg_left (ih _ _ F G hFG) (hκ _ _ _)

lemma Ex_nonneg (κ : ℕ → (ℕ → V) → V → ℝ) (hκ : ∀ T h y, 0 ≤ κ T h y) :
    ∀ m T (h : ℕ → V) (F : (ℕ → V) → ℝ), (∀ h', 0 ≤ F h') → 0 ≤ Ex κ m T h F := by
  intro m
  induction m with
  | zero => intro T h F hF; exact hF h
  | succ m ih =>
    intro T h F hF
    rw [Ex_succ]
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (hκ _ _ _) (ih _ _ F hF))

lemma Ex_add (κ : ℕ → (ℕ → V) → V → ℝ) :
    ∀ m T (h : ℕ → V) (F G : (ℕ → V) → ℝ),
      Ex κ m T h (fun h' => F h' + G h') = Ex κ m T h F + Ex κ m T h G := by
  intro m
  induction m with
  | zero => intro T h F G; rfl
  | succ m ih =>
    intro T h F G
    simp only [Ex_succ, ih, mul_add, Finset.sum_add_distrib]

lemma Ex_smul (κ : ℕ → (ℕ → V) → V → ℝ) :
    ∀ m T (h : ℕ → V) (c : ℝ) (F : (ℕ → V) → ℝ),
      Ex κ m T h (fun h' => c * F h') = c * Ex κ m T h F := by
  intro m
  induction m with
  | zero => intro T h c F; rfl
  | succ m ih =>
    intro T h c F
    simp only [Ex_succ, ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring

lemma Ex_sum {ι : Type} (κ : ℕ → (ℕ → V) → V → ℝ) (m T : ℕ) (h : ℕ → V) (s : Finset ι)
    (F : ι → (ℕ → V) → ℝ) :
    Ex κ m T h (fun h' => ∑ i ∈ s, F i h') = ∑ i ∈ s, Ex κ m T h (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := Ex_smul κ m T h 0 (fun _ => 0)
    simpa using this
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Ex_add, ih]

lemma Ex_congr (κ : ℕ → (ℕ → V) → V → ℝ) :
    ∀ m T (h : ℕ → V) (F G : (ℕ → V) → ℝ),
      (∀ h' : ℕ → V, (∀ i ≤ T, h' i = h i) → F h' = G h') → Ex κ m T h F = Ex κ m T h G := by
  intro m
  induction m with
  | zero => intro T h F G hFG; exact hFG h (fun _ _ => rfl)
  | succ m ih =>
    intro T h F G hFG
    rw [Ex_succ, Ex_succ]
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    apply ih
    intro h' hh'
    apply hFG
    intro i hi
    rw [hh' i (by omega), Function.update_of_ne (by omega)]

lemma Ex_local_mul (κ : ℕ → (ℕ → V) → V → ℝ) (m T : ℕ) (h : ℕ → V)
    (φ F : (ℕ → V) → ℝ) (hφ : ∀ h' : ℕ → V, (∀ i ≤ T, h' i = h i) → φ h' = φ h) :
    Ex κ m T h (fun h' => φ h' * F h') = φ h * Ex κ m T h F := by
  rw [← Ex_smul]
  apply Ex_congr
  intro h' hh'
  rw [hφ h' hh']

lemma Ex_const_le (κ : ℕ → (ℕ → V) → V → ℝ) (hκ : ∀ T h y, 0 ≤ κ T h y)
    (hκ1 : ∀ T h, ∑ y, κ T h y ≤ 1) :
    ∀ m T (h : ℕ → V) (c : ℝ), 0 ≤ c → Ex κ m T h (fun _ => c) ≤ c := by
  intro m
  induction m with
  | zero => intro T h c _; exact le_rfl
  | succ m ih =>
    intro T h c hc
    rw [Ex_succ]
    calc ∑ y, κ T h y * Ex κ m (T+1) (Function.update h (T+1) y) (fun _ => c)
        ≤ ∑ y, κ T h y * c := by
          apply Finset.sum_le_sum
          intro y _
          exact mul_le_mul_of_nonneg_left (ih _ _ c hc) (hκ _ _ _)
      _ = (∑ y, κ T h y) * c := by rw [Finset.sum_mul]
      _ ≤ 1 * c := mul_le_mul_of_nonneg_right (hκ1 T h) hc
      _ = c := one_mul c

/-- absorb a local kernel product into the kernel -/
lemma Ex_absorb (κ κ' : ℕ → (ℕ → V) → V → ℝ)
    (hloc : ∀ k (h h' : ℕ → V) y, (∀ i ≤ k, h' i = h i) → κ' k h' y = κ' k h y) :
    ∀ m T (h : ℕ → V) (F : (ℕ → V) → ℝ),
      Ex κ m T h (fun h' => (∏ k ∈ Finset.Ico T (T+m), κ' k h' (h' (k+1))) * F h')
        = Ex (fun k h y => κ k h y * κ' k h y) m T h F := by
  intro m
  induction m with
  | zero => intro T h F; simp [Ex_zero]
  | succ m ih =>
    intro T h F
    rw [Ex_succ, Ex_succ]
    apply Finset.sum_congr rfl
    intro y _
    have hsplit : ∀ h' : ℕ → V,
        (∏ k ∈ Finset.Ico T (T + (m+1)), κ' k h' (h' (k+1))) * F h'
          = κ' T h' (h' (T+1)) *
            ((∏ k ∈ Finset.Ico (T+1) (T+1+m), κ' k h' (h' (k+1))) * F h') := by
      intro h'
      rw [show T + (m+1) = (T+1+m) by omega,
        Finset.prod_eq_prod_Ico_succ_bot (by omega)]
      ring
    simp_rw [hsplit]
    rw [Ex_local_mul κ m (T+1) (Function.update h (T+1) y) (fun h' => κ' T h' (h' (T+1)))]
    · rw [ih]
      simp only [Function.update_self]
      rw [hloc T h (Function.update h (T+1) y) y]
      · ring
      · intro i hi; rw [Function.update_of_ne (by omega)]
    · intro h' hh'
      show κ' T h' (h' (T+1)) = κ' T _ ((Function.update h (T+1) y) (T+1))
      rw [hh' (T+1) le_rfl, hloc T (Function.update h (T+1) y) h']
      intro i hi; exact hh' i (by omega)


section Markov
variable (P : V → V → ℝ)

noncomputable def Pop (g : V → ℝ) : V → ℝ := fun x => ∑ y, P x y * g y

lemma Pop_iter_nonneg (hP : ∀ x y, 0 ≤ P x y) (g : V → ℝ) (hg : ∀ x, 0 ≤ g x) :
    ∀ j x, 0 ≤ (Pop P)^[j] g x := by
  intro j
  induction j with
  | zero => intro x; exact hg x
  | succ j ih =>
    intro x
    rw [Function.iterate_succ_apply']
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (hP x y) (ih y))

lemma stat_iter (D : V → ℝ) (hstat : ∀ y, ∑ x, D x * P x y = D y) (g : V → ℝ) :
    ∀ j, ∑ x, D x * (Pop P)^[j] g x = ∑ x, D x * g x := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← ih]
    simp only [Function.iterate_succ_apply', Pop, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [← hstat y, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    ring

noncomputable def kap (isNew : ℕ → Bool) (s : ℕ → ℕ) : ℕ → (ℕ → V) → V → ℝ :=
  fun T h y => if isNew T then P (h T) y else if y = h (s T) then 1 else 0

lemma kap_nonneg (hP : ∀ x y, 0 ≤ P x y) (isNew : ℕ → Bool) (s : ℕ → ℕ) :
    ∀ T h y, 0 ≤ kap P isNew s T h y := by
  intro T h y
  unfold kap
  split_ifs
  · exact hP _ _
  · norm_num
  · norm_num

lemma kap_sum_le (hP1 : ∀ x, ∑ y, P x y ≤ 1) (isNew : ℕ → Bool) (s : ℕ → ℕ) :
    ∀ T h, ∑ y, kap P isNew s T h y ≤ 1 := by
  intro T h
  unfold kap
  by_cases hT : isNew T = true
  · simp only [hT, if_true]; exact hP1 _
  · simp only [hT, Bool.false_eq_true, if_false]
    rw [Finset.sum_ite_eq']
    simp

lemma marginal (hP : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y ≤ 1)
    (isNew : ℕ → Bool) (s : ℕ → ℕ) (hs : ∀ T, s T ≤ T) (g : V → ℝ) (hg : ∀ x, 0 ≤ g x) :
    ∀ m T t, t ≤ T + m → ∃ a ≤ T, ∃ j, ∀ h : ℕ → V,
      Ex (kap P isNew s) m T h (fun h' => g (h' t)) ≤ (Pop P)^[j] g (h a) := by
  intro m
  induction m with
  | zero =>
    intro T t ht
    refine ⟨t, by omega, 0, fun h => ?_⟩
    simp [Ex_zero]
  | succ m ih =>
    intro T t ht
    by_cases htT : t ≤ T
    · refine ⟨t, htT, 0, fun h => ?_⟩
      rw [Ex_congr _ _ _ _ _ (fun _ => g (h t)) (fun h' hh' => by rw [hh' t htT])]
      exact Ex_const_le _ (kap_nonneg P hP isNew s) (kap_sum_le P hP1 isNew s) _ _ _ _ (hg _)
    · obtain ⟨a', ha', j', hj'⟩ := ih (T+1) t (by omega)
      by_cases haT : a' = T + 1
      · subst haT
        cases hnew : isNew T
        · refine ⟨s T, hs T, j', fun h => ?_⟩
          rw [Ex_succ]
          calc ∑ y, kap P isNew s T h y * Ex (kap P isNew s) m (T+1) (Function.update h (T+1) y)
                (fun h' => g (h' t))
              ≤ ∑ y, kap P isNew s T h y * (Pop P)^[j'] g (Function.update h (T+1) y (T+1)) := by
                apply Finset.sum_le_sum
                intro y _
                exact mul_le_mul_of_nonneg_left (hj' _) (kap_nonneg P hP isNew s _ _ _)
            _ = ∑ y, (if y = h (s T) then (1:ℝ) else 0) * (Pop P)^[j'] g y := by
                apply Finset.sum_congr rfl
                intro y _
                simp [kap, hnew]
            _ = (Pop P)^[j'] g (h (s T)) := by
                simp [ite_mul]
        · refine ⟨T, le_rfl, j'+1, fun h => ?_⟩
          rw [Ex_succ]
          calc ∑ y, kap P isNew s T h y * Ex (kap P isNew s) m (T+1) (Function.update h (T+1) y)
                (fun h' => g (h' t))
              ≤ ∑ y, kap P isNew s T h y * (Pop P)^[j'] g (Function.update h (T+1) y (T+1)) := by
                apply Finset.sum_le_sum
                intro y _
                exact mul_le_mul_of_nonneg_left (hj' _) (kap_nonneg P hP isNew s _ _ _)
            _ = ∑ y, P (h T) y * (Pop P)^[j'] g y := by
                apply Finset.sum_congr rfl
                intro y _
                simp [kap, hnew]
            _ = (Pop P)^[j'+1] g (h T) := by
                rw [Function.iterate_succ_apply']
                rfl
      · refine ⟨a', by omega, j', fun h => ?_⟩
        rw [Ex_succ]
        have hnn : 0 ≤ (Pop P)^[j'] g (h a') := Pop_iter_nonneg P hP g hg j' _
        calc ∑ y, kap P isNew s T h y * Ex (kap P isNew s) m (T+1) (Function.update h (T+1) y)
              (fun h' => g (h' t))
            ≤ ∑ y, kap P isNew s T h y * (Pop P)^[j'] g (Function.update h (T+1) y a') := by
              apply Finset.sum_le_sum
              intro y _
              exact mul_le_mul_of_nonneg_left (hj' _) (kap_nonneg P hP isNew s _ _ _)
          _ = (∑ y, kap P isNew s T h y) * (Pop P)^[j'] g (h a') := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro y _
              rw [Function.update_of_ne haT]
          _ ≤ 1 * (Pop P)^[j'] g (h a') :=
              mul_le_mul_of_nonneg_right (kap_sum_le P hP1 isNew s T h) hnn
          _ = (Pop P)^[j'] g (h a') := one_mul _

end Markov

lemma pow_apply_Ex (H : Matrix V V ℝ) : ∀ m T (h : ℕ → V) (z : V),
    (H ^ m) (h T) z = Ex (fun _ _ _ => (1:ℝ)) m T h
      (fun h' => (∏ k ∈ Finset.Ico T (T+m), H (h' k) (h' (k+1))) *
        (if h' (T+m) = z then 1 else 0)) := by
  intro m
  induction m with
  | zero =>
    intro T h z
    simp [Ex_zero, Matrix.one_apply]
  | succ m ih =>
    intro T h z
    rw [pow_succ', Matrix.mul_apply, Ex_succ]
    apply Finset.sum_congr rfl
    intro y _
    have hsplit : ∀ h' : ℕ → V,
        (∏ k ∈ Finset.Ico T (T + (m+1)), H (h' k) (h' (k+1))) *
          (if h' (T + (m+1)) = z then (1:ℝ) else 0)
          = H (h' T) (h' (T+1)) *
            ((∏ k ∈ Finset.Ico (T+1) (T+1+m), H (h' k) (h' (k+1))) *
              (if h' (T+1+m) = z then 1 else 0)) := by
      intro h'
      rw [show T + (m+1) = (T+1+m) by omega,
        Finset.prod_eq_prod_Ico_succ_bot (by omega)]
      ring
    simp_rw [hsplit]
    rw [Ex_local_mul _ m (T+1) (Function.update h (T+1) y) (fun h' => H (h' T) (h' (T+1)))]
    · have := ih (T+1) (Function.update h (T+1) y) z
      simp only [Function.update_self] at this
      rw [this]
      simp only [Function.update_self, Function.update_of_ne (show T ≠ T + 1 by omega)]
      ring
    · intro h' hh'
      show H (h' T) (h' (T+1)) = H _ ((Function.update h (T+1) y) (T+1))
      rw [hh' (T+1) le_rfl, hh' T (by omega)]


section Pairing
variable {N : ℕ}

def PairOn (S : Finset (Fin N)) : Finset (Fin N → Fin N) :=
  Finset.univ.filter (fun σ => (∀ k ∈ S, σ k ∈ S ∧ σ k ≠ k ∧ σ (σ k) = k) ∧ ∀ k ∉ S, σ k = k)

def swapExt (m l : Fin N) (τ : Fin N → Fin N) : Fin N → Fin N :=
  fun k => if k = m then l else if k = l then m else τ k

def dfact : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | (c+2) => (c+1) * dfact c

lemma mem_PairOn (S : Finset (Fin N)) (σ : Fin N → Fin N) :
    σ ∈ PairOn S ↔ (∀ k ∈ S, σ k ∈ S ∧ σ k ≠ k ∧ σ (σ k) = k) ∧ ∀ k ∉ S, σ k = k := by
  simp [PairOn]

lemma card_PairOn : ∀ c (S : Finset (Fin N)), S.card = c → (PairOn S).card ≤ dfact c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro S hS
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    rw [Finset.card_eq_zero] at hS
    subst hS
    have : PairOn (∅ : Finset (Fin N)) ⊆ {id} := by
      intro σ hσ
      rw [mem_PairOn] at hσ
      rw [Finset.mem_singleton]
      funext k
      exact hσ.2 k (Finset.notMem_empty k)
    calc (PairOn (∅ : Finset (Fin N))).card ≤ ({id} : Finset (Fin N → Fin N)).card :=
          Finset.card_le_card this
      _ = dfact 0 := by simp [dfact]
  · obtain ⟨m, hm⟩ : S.Nonempty := by
      rw [← Finset.card_pos]; omega
    have hsub : PairOn S ⊆ (S.erase m).biUnion
        (fun l => (PairOn ((S.erase m).erase l)).image (swapExt m l)) := by
      intro σ hσ
      rw [mem_PairOn] at hσ
      obtain ⟨h1, h2⟩ := hσ
      obtain ⟨hmS, hmne, hmm⟩ := h1 m hm
      rw [Finset.mem_biUnion]
      refine ⟨σ m, Finset.mem_erase.mpr ⟨hmne, hmS⟩, ?_⟩
      rw [Finset.mem_image]
      refine ⟨fun k => if k = m ∨ k = σ m then k else σ k, ?_, ?_⟩
      · rw [mem_PairOn]
        constructor
        · intro k hk
          simp only [Finset.mem_erase] at hk
          obtain ⟨hkl, hkm, hkS⟩ := hk
          obtain ⟨hkS', hkne, hkk⟩ := h1 k hkS
          have hσk_m : σ k ≠ m := by
            intro h; apply hkl; rw [← hkk, h]
          have hσk_l : σ k ≠ σ m := by
            intro h; apply hkm; rw [← hkk, h, hmm]
          simp only [hkm, hkl, or_self, if_false, hσk_m, hσk_l, Finset.mem_erase, ne_eq,
            not_false_eq_true, true_and, hkS', hkne, hkk]
        · intro k hk
          by_cases hkm : k = m
          · simp [hkm]
          by_cases hkl : k = σ m
          · simp [hkl]
          simp only [hkm, hkl, or_self, if_false]
          apply h2
          intro hkS
          apply hk
          simp [Finset.mem_erase, hkm, hkl, hkS]
      · funext k
        unfold swapExt
        by_cases hkm : k = m
        · subst hkm; simp
        by_cases hkl : k = σ m
        · subst hkl; simp [hkm, hmm]
        simp [hkm, hkl]
    calc (PairOn S).card
        ≤ ((S.erase m).biUnion
            (fun l => (PairOn ((S.erase m).erase l)).image (swapExt m l))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ l ∈ S.erase m, ((PairOn ((S.erase m).erase l)).image (swapExt m l)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ l ∈ S.erase m, (PairOn ((S.erase m).erase l)).card :=
          Finset.sum_le_sum (fun l _ => Finset.card_image_le)
      _ ≤ dfact c := by
          obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
          rcases Nat.eq_zero_or_pos c' with hc' | hc'
          · subst hc'
            have : S.erase m = ∅ := by
              rw [← Finset.card_eq_zero, Finset.card_erase_of_mem hm, hS]
            rw [this]; simp
          · obtain ⟨c'', rfl⟩ : ∃ c'', c' = c'' + 1 := ⟨c' - 1, by omega⟩
            calc ∑ l ∈ S.erase m, (PairOn ((S.erase m).erase l)).card
                ≤ ∑ l ∈ S.erase m, dfact c'' := by
                  apply Finset.sum_le_sum
                  intro l hl
                  apply ih c'' (by omega)
                  rw [Finset.card_erase_of_mem hl, Finset.card_erase_of_mem hm, hS]
                  omega
              _ = (c'' + 1) * dfact c'' := by
                  rw [Finset.sum_const, Finset.card_erase_of_mem hm, hS, smul_eq_mul, Nat.add_sub_cancel]
              _ = dfact (c'' + 1 + 1) := rfl

lemma exists_pair {β : Type} [DecidableEq β] (L : Fin N → β) :
    ∀ c (S : Finset (Fin N)), S.card = c →
      (∀ x, Even ((S.filter (fun k => L k = x)).card)) →
      ∃ σ ∈ PairOn S, ∀ k ∈ S, L (σ k) = L k := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro S hS hev
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    rw [Finset.card_eq_zero] at hS
    subst hS
    refine ⟨id, ?_, by simp⟩
    rw [mem_PairOn]; simp
  · obtain ⟨m, hm⟩ : S.Nonempty := by
      rw [← Finset.card_pos]; omega
    have hmc : m ∈ S.filter (fun k => L k = L m) := by simp [hm]
    have hcard2 : 1 < (S.filter (fun k => L k = L m)).card := by
      have h1 : 0 < (S.filter (fun k => L k = L m)).card := Finset.card_pos.mpr ⟨m, hmc⟩
      obtain ⟨r, hr⟩ := hev (L m)
      omega
    obtain ⟨l, hl, hlm⟩ := Finset.exists_mem_ne hcard2 m
    simp only [Finset.mem_filter] at hl
    obtain ⟨hlS, hLl⟩ := hl
    set S' := (S.erase m).erase l with hS'
    have hlS' : l ∈ S.erase m := Finset.mem_erase.mpr ⟨hlm, hlS⟩
    have hcardS' : S'.card = c - 2 := by
      rw [hS', Finset.card_erase_of_mem hlS', Finset.card_erase_of_mem hm, hS]; omega
    have hev' : ∀ x, Even ((S'.filter (fun k => L k = x)).card) := by
      intro x
      rw [hS', Finset.filter_erase, Finset.filter_erase]
      by_cases hx : L m = x
      · have hm' : m ∈ S.filter (fun k => L k = x) := by simp [hm, hx]
        have hl' : l ∈ (S.filter (fun k => L k = x)).erase m := by
          simp [hlm, hlS, hLl, hx]
        rw [Finset.card_erase_of_mem hl', Finset.card_erase_of_mem hm']
        have h2 : 2 ≤ (S.filter (fun k => L k = x)).card := by
          have := Finset.card_le_card (show ({m, l} : Finset (Fin N)) ⊆ S.filter (fun k => L k = x) by
            intro k hk
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl
            · exact hm'
            · simp [hlS, hLl, hx])
          rw [Finset.card_pair (Ne.symm hlm)] at this
          exact this
        obtain ⟨r, hr⟩ := hev x
        rw [show (S.filter (fun k => L k = x)).card - 1 - 1 = (S.filter (fun k => L k = x)).card - 2 by omega]
        exact ⟨r - 1, by omega⟩
      · have hm' : m ∉ S.filter (fun k => L k = x) := by simp [hx]
        have hl' : l ∉ (S.filter (fun k => L k = x)).erase m := by simp [hLl, hx]
        rw [Finset.erase_eq_of_notMem hl', Finset.erase_eq_of_notMem hm']
        exact hev x
    obtain ⟨τ, hτ, hτL⟩ := ih (c - 2) (by omega) S' hcardS' hev'
    rw [mem_PairOn] at hτ
    obtain ⟨t1, t2⟩ := hτ
    have hmS' : m ∉ S' := by simp [hS']
    have hlS'' : l ∉ S' := by simp [hS']
    have τm : τ m = m := t2 m hmS'
    have τl : τ l = l := t2 l hlS''
    have memS' : ∀ k, k ∈ S' ↔ k ≠ l ∧ k ≠ m ∧ k ∈ S := by
      intro k; simp [hS', Finset.mem_erase]
    refine ⟨swapExt m l τ, ?_, ?_⟩
    · rw [mem_PairOn]
      constructor
      · intro k hk
        unfold swapExt
        by_cases hkm : k = m
        · subst hkm; simp [hlS, hlm, Ne.symm hlm]
        by_cases hkl : k = l
        · subst hkl; simp [hm, hlm, Ne.symm hlm]
        have hkS' : k ∈ S' := (memS' k).mpr ⟨hkl, hkm, hk⟩
        obtain ⟨a1, a2, a3⟩ := t1 k hkS'
        obtain ⟨b1, b2, b3⟩ := (memS' (τ k)).mp a1
        simp [hkm, hkl, b1, b2, b3, a2, a3]
      · intro k hk
        unfold swapExt
        have hkm : k ≠ m := fun h => hk (h ▸ hm)
        have hkl : k ≠ l := fun h => hk (h ▸ hlS)
        have hkS' : k ∉ S' := fun h => hk ((memS' k).mp h).2.2
        simp [hkm, hkl, t2 k hkS']
    · intro k hk
      unfold swapExt
      by_cases hkm : k = m
      · subst hkm; simp [hLl, Ne.symm hlm]
      by_cases hkl : k = l
      · subst hkl; simp [hLl, hkm]
      have hkS' : k ∈ S' := (memS' k).mpr ⟨hkl, hkm, hk⟩
      obtain ⟨a1, a2, a3⟩ := t1 k hkS'
      obtain ⟨b1, b2, b3⟩ := (memS' (τ k)).mp a1
      simp [hkm, hkl, b1, b2, hτL k hkS']

lemma dfact_two_mul (n : ℕ) : dfact (2 * n) * (2 ^ n * n.factorial) = (2 * n).factorial := by
  induction n with
  | zero => simp [dfact]
  | succ n ih =>
    rw [show 2 * (n+1) = 2 * n + 1 + 1 by ring]
    show (2 * n + 1) * dfact (2 * n) * (2 ^ (n+1) * (n+1).factorial) = (2 * n + 1 + 1).factorial
    rw [Nat.factorial_succ (2*n+1), Nat.factorial_succ (2*n), ← ih, Nat.factorial_succ n, pow_succ]
    ring

end Pairing


section Rad
variable {E : Type} [Fintype E] [DecidableEq E]

def sgn (eps : Finset E) (x : E) : ℝ := if x ∈ eps then 1 else -1

def sgnO (eps : Finset E) : Option E → ℝ
  | none => 0
  | some x => sgn eps x

noncomputable def radE (F : Finset E → ℝ) : ℝ :=
  ∑ eps : Finset E, ((1:ℝ) / 2) ^ Fintype.card E * F eps

lemma abs_sgnO_le (eps : Finset E) (o : Option E) : |sgnO eps o| ≤ 1 := by
  cases o with
  | none => simp [sgnO]
  | some x => simp only [sgnO, sgn]; split_ifs <;> simp

lemma radE_prod_le_one {N : ℕ} (L : Fin N → Option E) :
    radE (fun eps => ∏ k, sgnO eps (L k)) ≤ 1 := by
  unfold radE
  have hw : (0:ℝ) ≤ ((1:ℝ) / 2) ^ Fintype.card E := by positivity
  calc ∑ eps : Finset E, ((1:ℝ) / 2) ^ Fintype.card E * ∏ k, sgnO eps (L k)
      ≤ ∑ eps : Finset E, ((1:ℝ) / 2) ^ Fintype.card E * 1 := by
        apply Finset.sum_le_sum
        intro eps _
        apply mul_le_mul_of_nonneg_left _ hw
        have : |∏ k, sgnO eps (L k)| ≤ 1 := by
          rw [Finset.abs_prod]
          apply Finset.prod_le_one (fun k _ => abs_nonneg _) (fun k _ => abs_sgnO_le eps (L k))
        exact le_trans (le_abs_self _) this
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul, mul_one]
        push_cast
        rw [← mul_pow]; norm_num

lemma sgnO_symmDiff (eps : Finset E) (x : E) (o : Option E) :
    sgnO (symmDiff eps {x}) o = (if o = some x then -1 else 1) * sgnO eps o := by
  cases o with
  | none => simp [sgnO]
  | some y =>
    simp only [sgnO, sgn, Option.some.injEq, Finset.mem_symmDiff, Finset.mem_singleton]
    by_cases hy : y = x
    · subst hy; by_cases h : y ∈ eps <;> simp [h]
    · simp [hy]

lemma radE_even {N : ℕ} (L : Fin N → Option E)
    (h0 : radE (fun eps => ∏ k, sgnO eps (L k)) ≠ 0) :
    ∀ o : Option E, Even ((Finset.univ.filter (fun k => L k = o)).card) := by
  intro o
  cases o with
  | none =>
    have : Finset.univ.filter (fun k => L k = none) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro k _ hk
      apply h0
      unfold radE
      apply Finset.sum_eq_zero
      intro eps _
      show ((1:ℝ) / 2) ^ Fintype.card E * ∏ k, sgnO eps (L k) = 0
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (show sgnO eps (L k) = 0 by rw [hk]; rfl), mul_zero]
    rw [this]; simp
  | some x =>
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    apply h0
    set f : Finset E → ℝ := fun eps => ((1:ℝ) / 2) ^ Fintype.card E * ∏ k, sgnO eps (L k) with hf
    have hτ : Function.Involutive (fun eps : Finset E => symmDiff eps {x}) := by
      intro eps; simp [symmDiff_symmDiff_cancel_right]
    have hflip : ∀ eps, f (symmDiff eps {x}) = - f eps := by
      intro eps
      simp only [hf, sgnO_symmDiff, Finset.prod_mul_distrib]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
        Odd.neg_one_pow hodd]
      ring
    have hsum : ∑ eps, f eps = ∑ eps, f (symmDiff eps {x}) :=
      (Fintype.sum_equiv (hτ.toPerm _) _ _ (fun eps => rfl)).symm
    have : ∑ eps, f eps = - ∑ eps, f eps := by
      calc ∑ eps, f eps = ∑ eps, f (symmDiff eps {x}) := hsum
        _ = ∑ eps, -f eps := Finset.sum_congr rfl (fun eps _ => hflip eps)
        _ = - ∑ eps, f eps := Finset.sum_neg_distrib _
    unfold radE
    change ∑ eps, f eps = 0
    linarith

end Rad


lemma amgm (S : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ k ∈ S, 0 ≤ f k) (c : ℕ) (hc : S.card = c)
    (hc1 : 1 ≤ c) : ∏ k ∈ S, f k ≤ ∑ k ∈ S, (c:ℝ)⁻¹ * f k ^ c := by
  have hcpos : (0:ℝ) < c := by exact_mod_cast hc1
  have := Real.geom_mean_le_arith_mean_weighted (s := S) (fun _ => (c:ℝ)⁻¹) (fun k => f k ^ c)
    (fun _ _ => by positivity) (by rw [Finset.sum_const, hc, nsmul_eq_mul]; field_simp)
    (fun k hk => pow_nonneg (hf k hk) c)
  calc ∏ k ∈ S, f k = ∏ k ∈ S, (f k ^ c) ^ (c:ℝ)⁻¹ := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [Real.pow_rpow_inv_natCast (hf k hk) (by omega)]
    _ ≤ _ := this

section Graph
variable {n1 n2 : ℕ}

abbrev VV (n1 n2 : ℕ) := Fin n1 ⊕ Fin n2

def lab : VV n1 n2 → VV n1 n2 → Option (Fin n1 × Fin n2)
  | Sum.inl i, Sum.inr j => some (i, j)
  | Sum.inr j, Sum.inl i => some (i, j)
  | _, _ => none

lemma lab_comm (u v : VV n1 n2) : lab u v = lab v u := by
  cases u <;> cases v <;> rfl

lemma lab_side {u v : VV n1 n2} (h : lab u v ≠ none) : v.isLeft = !u.isLeft := by
  cases u <;> cases v <;> simp_all [lab]

lemma lab_eq_same {u v u' v' : VV n1 n2} {e : Fin n1 × Fin n2} (h1 : lab u v = some e)
    (h2 : lab u' v' = some e) (h3 : u.isLeft = u'.isLeft) : u = u' ∧ v = v' := by
  have h := h1.trans h2.symm
  clear h2
  cases u <;> cases v <;> cases u' <;> cases v' <;> simp_all [lab]

lemma lab_eq_diff {u v u' v' : VV n1 n2} {e : Fin n1 × Fin n2} (h1 : lab u v = some e)
    (h2 : lab u' v' = some e) (h3 : u.isLeft ≠ u'.isLeft) : u = v' ∧ v = u' := by
  have h := h1.trans h2.symm
  clear h2
  cases u <;> cases v <;> cases u' <;> cases v' <;> simp_all [lab]

def aO (a : Fin n1 → Fin n2 → ℝ) : Option (Fin n1 × Fin n2) → ℝ
  | none => 0
  | some e => a e.1 e.2

def AA (a : Fin n1 → Fin n2 → ℝ) (u v : VV n1 n2) : ℝ := aO a (lab u v)
noncomputable def BB (a : Fin n1 → Fin n2 → ℝ) (u v : VV n1 n2) : ℝ := (AA a u v) ^ 2
noncomputable def DD (a : Fin n1 → Fin n2 → ℝ) (u : VV n1 n2) : ℝ := ∑ v, BB a u v
noncomputable def PP (a : Fin n1 → Fin n2 → ℝ) (u v : VV n1 n2) : ℝ := BB a u v / DD a u

variable (a : Fin n1 → Fin n2 → ℝ)

lemma BB_nonneg (u v : VV n1 n2) : 0 ≤ BB a u v := sq_nonneg _
lemma DD_nonneg (u : VV n1 n2) : 0 ≤ DD a u := Finset.sum_nonneg (fun v _ => BB_nonneg a u v)
lemma PP_nonneg (u v : VV n1 n2) : 0 ≤ PP a u v := div_nonneg (BB_nonneg a u v) (DD_nonneg a u)

lemma BB_eq (u v : VV n1 n2) : BB a u v = DD a u * PP a u v := by
  by_cases hD : DD a u = 0
  · have : BB a u v = 0 := by
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => BB_nonneg a u w)).mp hD
      exact h0 v (Finset.mem_univ v)
    rw [this, hD, zero_mul]
  · unfold PP; field_simp

lemma PP_sum_le (u : VV n1 n2) : ∑ v, PP a u v ≤ 1 := by
  unfold PP
  rw [← Finset.sum_div]
  by_cases hD : DD a u = 0
  · rw [show ∑ v, BB a u v = DD a u from rfl, hD]; simp
  · rw [show ∑ v, BB a u v = DD a u from rfl, div_self hD]

lemma PP_stat (v : VV n1 n2) : ∑ u, DD a u * PP a u v = DD a v := by
  simp_rw [← BB_eq]
  unfold DD BB AA
  apply Finset.sum_congr rfl
  intro u _
  rw [lab_comm]

lemma alt (h : ℕ → VV n1 n2) (N : ℕ) (hall : ∀ k < N, lab (h k) (h (k+1)) ≠ none) :
    ∀ d k, k + d ≤ N → ((h (k+d)).isLeft = (h k).isLeft ↔ Even d) := by
  intro d
  induction d with
  | zero => intro k _; simp
  | succ d ih =>
    intro k hk
    have h1 := lab_side (hall (k+d) (by omega))
    rw [show k + (d+1) = k + d + 1 by ring, h1, Nat.even_add_one, ← ih k (by omega)]
    cases (h (k+d)).isLeft <;> cases (h k).isLeft <;> simp

end Graph


section PerPair
variable {n1 n2 : ℕ} (a : Fin n1 → Fin n2 → ℝ)

def Lh (h : ℕ → VV n1 n2) (k : ℕ) : Option (Fin n1 × Fin n2) := lab (h k) (h (k+1))

def isNewF (σN : ℕ → ℕ) : ℕ → Bool := fun k => decide (k < σN k)
def sfun (σN : ℕ → ℕ) : ℕ → ℕ := fun k => min k (if Even (k - σN k) then σN k + 1 else σN k)
def newN (N : ℕ) (σN : ℕ → ℕ) : Finset ℕ := (Finset.range N).filter (fun k => k < σN k)

lemma sfun_le (σN : ℕ → ℕ) (k : ℕ) : sfun σN k ≤ k := min_le_left _ _

lemma kap_loc {W : Type} [Fintype W] [DecidableEq W] (P : W → W → ℝ) (isNew : ℕ → Bool)
    (s : ℕ → ℕ) (hs : ∀ k, s k ≤ k) :
    ∀ k (h h' : ℕ → W) y, (∀ i ≤ k, h' i = h i) → kap P isNew s k h' y = kap P isNew s k h y := by
  intro k h h' y hh
  unfold kap
  rw [hh k le_rfl, hh (s k) (hs k)]

lemma prod_pair (N : ℕ) (σN : ℕ → ℕ) (hσ : ∀ k < N, σN k < N ∧ σN k ≠ k ∧ σN (σN k) = k)
    (x : ℕ → ℝ) (hx : ∀ k < N, x (σN k) = x k) :
    ∏ k ∈ Finset.range N, x k = ∏ k ∈ newN N σN, x k ^ 2 := by
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.range N) (fun k => k < σN k)]
  have : ∏ k ∈ (Finset.range N).filter (fun k => ¬ k < σN k), x k = ∏ k ∈ newN N σN, x k := by
    apply Finset.prod_nbij' σN σN
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, newN] at hk ⊢
      obtain ⟨h1, h2, h3⟩ := hσ k hk.1
      refine ⟨h1, ?_⟩; rw [h3]; omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, newN] at hk ⊢
      obtain ⟨h1, h2, h3⟩ := hσ k hk.1
      refine ⟨h1, ?_⟩; rw [h3]; omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      exact (hσ k hk.1).2.2
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, newN] at hk
      exact (hσ k hk.1).2.2
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      exact (hx k hk.1).symm
  rw [this, show (Finset.range N).filter (fun k => k < σN k) = newN N σN from rfl,
    ← Finset.prod_mul_distrib]
  simp [sq]

lemma card_newN (N : ℕ) (σN : ℕ → ℕ) (hσ : ∀ k < N, σN k < N ∧ σN k ≠ k ∧ σN (σN k) = k) :
    (newN N σN).card * 2 = N := by
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.range N)
    (fun k => k < σN k)
  have h2 : ((Finset.range N).filter (fun k => ¬ k < σN k)).card = (newN N σN).card := by
    apply Finset.card_nbij' σN σN
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_range, newN, Set.mem_setOf_eq] at hk ⊢
      obtain ⟨h1, h2, h3⟩ := hσ k hk.1
      refine ⟨h1, ?_⟩; rw [h3]; omega
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_range, newN, Set.mem_setOf_eq] at hk ⊢
      obtain ⟨h1, h2, h3⟩ := hσ k hk.1
      refine ⟨h1, ?_⟩; rw [h3]; omega
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk
      exact (hσ k hk.1).2.2
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_range, newN, Set.mem_setOf_eq] at hk
      exact (hσ k hk.1).2.2
  rw [Finset.card_range, h2] at h1
  unfold newN at h1 ⊢
  omega

lemma zero_mem_newN (N : ℕ) (hN : 0 < N) (σN : ℕ → ℕ)
    (hσ : ∀ k < N, σN k < N ∧ σN k ≠ k ∧ σN (σN k) = k) : 0 ∈ newN N σN := by
  simp only [newN, Finset.mem_filter, Finset.mem_range]
  have := (hσ 0 hN).2.1
  omega

lemma pointwise (N : ℕ) (hN : 0 < N) (σN : ℕ → ℕ)
    (hσ : ∀ k < N, σN k < N ∧ σN k ≠ k ∧ σN (σN k) = k) (h : ℕ → VV n1 n2) :
    (if ∀ k < N, Lh h (σN k) = Lh h k then (1:ℝ) else 0) *
        ∏ k ∈ Finset.range N, AA a (h k) (h (k+1))
      ≤ DD a (h 0) * ((∏ k ∈ Finset.range N,
          kap (PP a) (isNewF σN) (sfun σN) k h (h (k+1))) *
          ∏ k ∈ (newN N σN).erase 0, DD a (h k)) := by
  have hRHS : 0 ≤ DD a (h 0) * ((∏ k ∈ Finset.range N,
          kap (PP a) (isNewF σN) (sfun σN) k h (h (k+1))) *
          ∏ k ∈ (newN N σN).erase 0, DD a (h k)) :=
    mul_nonneg (DD_nonneg a _) (mul_nonneg
      (Finset.prod_nonneg (fun k _ => kap_nonneg _ (PP_nonneg a) _ _ _ _ _))
      (Finset.prod_nonneg (fun k _ => DD_nonneg a _)))
  by_cases hc : ∀ k < N, Lh h (σN k) = Lh h k
  swap
  · rw [if_neg hc, zero_mul]; exact hRHS
  rw [if_pos hc, one_mul]
  by_cases hall : ∀ k < N, lab (h k) (h (k+1)) ≠ none
  swap
  · push Not at hall
    obtain ⟨k, hk, hk0⟩ := hall
    rw [Finset.prod_eq_zero (Finset.mem_range.mpr hk) (by simp [AA, hk0, aO])]
    exact hRHS
  apply le_of_eq
  have e1 : ∏ k ∈ Finset.range N, AA a (h k) (h (k+1))
      = ∏ k ∈ newN N σN, BB a (h k) (h (k+1)) := by
    rw [prod_pair N σN hσ (fun k => AA a (h k) (h (k+1)))]
    · rfl
    · intro k hk
      have := hc k hk
      unfold Lh at this
      show aO a (lab (h (σN k)) (h (σN k + 1))) = aO a (lab (h k) (h (k+1)))
      rw [this]
  have hold : ∀ k ∈ (Finset.range N).filter (fun k => ¬ k < σN k),
      kap (PP a) (isNewF σN) (sfun σN) k h (h (k+1)) = 1 := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkN, hknew⟩ := hk
    obtain ⟨j1, j2, j3⟩ := hσ k hkN
    have hjk : σN k < k := by omega
    have hLj : Lh h (σN k) = Lh h k := hc k hkN
    obtain ⟨e, he⟩ : ∃ e, Lh h (σN k) = some e :=
      Option.ne_none_iff_exists'.mp (hall (σN k) j1)
    have he' : Lh h k = some e := hLj ▸ he
    have halt := alt h N hall (k - σN k) (σN k) (by omega)
    rw [show σN k + (k - σN k) = k by omega] at halt
    have key : h (k+1) = h (sfun σN k) := by
      unfold sfun
      by_cases hev : Even (k - σN k)
      · rw [if_pos hev, min_eq_right (by omega)]
        exact (lab_eq_same he' he (halt.mpr hev)).2
      · rw [if_neg hev, min_eq_right (by omega)]
        exact (lab_eq_diff he' he (fun hh => hev (halt.mp hh))).2
    unfold kap isNewF
    simp [hknew, key]
  have e2 : ∏ k ∈ Finset.range N, kap (PP a) (isNewF σN) (sfun σN) k h (h (k+1))
      = ∏ k ∈ newN N σN, PP a (h k) (h (k+1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.range N) (fun k => k < σN k),
      Finset.prod_eq_one hold, mul_one]
    apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_filter] at hk
    simp [kap, isNewF, hk.2]
  have hz := zero_mem_newN N hN σN hσ
  calc ∏ k ∈ Finset.range N, AA a (h k) (h (k+1))
      = ∏ k ∈ newN N σN, BB a (h k) (h (k+1)) := e1
    _ = ∏ k ∈ newN N σN, (DD a (h k) * PP a (h k) (h (k+1))) :=
        Finset.prod_congr rfl (fun k _ => BB_eq a _ _)
    _ = (∏ k ∈ newN N σN, DD a (h k)) * ∏ k ∈ newN N σN, PP a (h k) (h (k+1)) :=
        Finset.prod_mul_distrib
    _ = (DD a (h 0) * ∏ k ∈ (newN N σN).erase 0, DD a (h k)) *
          ∏ k ∈ newN N σN, PP a (h k) (h (k+1)) := by
        rw [Finset.mul_prod_erase _ (fun k => DD a (h k)) hz]
    _ = _ := by rw [e2]; ring


theorem pair_bound (n : ℕ) (hn : 1 ≤ n) (σN : ℕ → ℕ)
    (hσ : ∀ k < 2*n, σN k < 2*n ∧ σN k ≠ k ∧ σN (σN k) = k) :
    ∑ x : VV n1 n2, Ex (fun _ _ _ => (1:ℝ)) (2*n) 0 (fun _ => x)
      (fun h => (if ∀ k < 2*n, Lh h (σN k) = Lh h k then (1:ℝ) else 0) *
        ∏ k ∈ Finset.range (2*n), AA a (h k) (h (k+1)))
      ≤ ∑ u : VV n1 n2, DD a u ^ n := by
  have hN : 0 < 2*n := by omega
  have hκ0 : ∀ T (h : ℕ → VV n1 n2) y, 0 ≤ kap (PP a) (isNewF σN) (sfun σN) T h y :=
    kap_nonneg _ (PP_nonneg a) _ _
  have hκ1 := kap_sum_le _ (PP_sum_le a) (isNewF σN) (sfun σN)
  have hloc := kap_loc (PP a) (isNewF σN) (sfun σN) (sfun_le σN)
  have hz := zero_mem_newN (2*n) hN σN hσ
  have hS : ((newN (2*n) σN).erase 0).card = n - 1 := by
    rw [Finset.card_erase_of_mem hz]
    have := card_newN (2*n) σN hσ
    omega
  have step1 : ∀ x : VV n1 n2, Ex (fun _ _ _ => (1:ℝ)) (2*n) 0 (fun _ => x)
      (fun h => (if ∀ k < 2*n, Lh h (σN k) = Lh h k then (1:ℝ) else 0) *
        ∏ k ∈ Finset.range (2*n), AA a (h k) (h (k+1)))
      ≤ DD a x * Ex (kap (PP a) (isNewF σN) (sfun σN)) (2*n) 0 (fun _ => x)
          (fun h => ∏ k ∈ (newN (2*n) σN).erase 0, DD a (h k)) := by
    intro x
    calc _ ≤ Ex (fun _ _ _ => (1:ℝ)) (2*n) 0 (fun _ => x)
          (fun h => DD a (h 0) * ((∏ k ∈ Finset.range (2*n),
            kap (PP a) (isNewF σN) (sfun σN) k h (h (k+1))) *
            ∏ k ∈ (newN (2*n) σN).erase 0, DD a (h k))) :=
          Ex_mono _ (fun _ _ _ => zero_le_one) _ _ _ _ _
            (fun h => pointwise a (2*n) hN σN hσ h)
      _ = DD a x * Ex (fun _ _ _ => (1:ℝ)) (2*n) 0 (fun _ => x)
          (fun h => (∏ k ∈ Finset.range (2*n),
            kap (PP a) (isNewF σN) (sfun σN) k h (h (k+1))) *
            ∏ k ∈ (newN (2*n) σN).erase 0, DD a (h k)) :=
          Ex_local_mul _ _ _ _ (fun h => DD a (h 0)) _ (fun h' hh' => by
            show DD a (h' 0) = DD a x
            rw [hh' 0 le_rfl])
      _ = _ := by
          congr 1
          have := Ex_absorb (fun _ _ _ => (1:ℝ)) (kap (PP a) (isNewF σN) (sfun σN)) hloc
            (2*n) 0 (fun _ => x) (fun h => ∏ k ∈ (newN (2*n) σN).erase 0, DD a (h k))
          simp only [zero_add, one_mul] at this
          rw [Finset.range_eq_Ico, this]
  calc _ ≤ ∑ x : VV n1 n2, DD a x * Ex (kap (PP a) (isNewF σN) (sfun σN)) (2*n) 0 (fun _ => x)
          (fun h => ∏ k ∈ (newN (2*n) σN).erase 0, DD a (h k)) :=
        Finset.sum_le_sum (fun x _ => step1 x)
    _ ≤ ∑ u : VV n1 n2, DD a u ^ n := by
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · have hn1 : n = 1 := by omega
        have hE : (newN (2*n) σN).erase 0 = ∅ := Finset.card_eq_zero.mp (by rw [hS, hn1])
        rw [hE]
        simp only [Finset.prod_empty]
        calc ∑ x : VV n1 n2, DD a x * Ex (kap (PP a) (isNewF σN) (sfun σN)) (2*n) 0
              (fun _ => x) (fun _ => (1:ℝ))
            ≤ ∑ x : VV n1 n2, DD a x * 1 :=
              Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
                (Ex_const_le _ hκ0 hκ1 _ _ _ 1 zero_le_one) (DD_nonneg a x))
          _ = ∑ u : VV n1 n2, DD a u ^ n := by simp [hn1]
      · set S := (newN (2*n) σN).erase 0 with hSdef
        set c : ℝ := ((n - 1 : ℕ) : ℝ)⁻¹ with hc
        have hcpos : (0:ℝ) < ((n - 1 : ℕ) : ℝ) := by
          have : 1 ≤ n - 1 := by omega
          exact_mod_cast this
        have hmarg : ∀ k ∈ S, ∑ x : VV n1 n2, DD a x *
            Ex (kap (PP a) (isNewF σN) (sfun σN)) (2*n) 0 (fun _ => x)
              (fun h => DD a (h k) ^ (n-1)) ≤ ∑ u : VV n1 n2, DD a u ^ n := by
          intro k hk
          have hkN : k < 2*n := by
            rw [hSdef, Finset.mem_erase] at hk
            simp only [newN, Finset.mem_filter, Finset.mem_range] at hk
            exact hk.2.1
          obtain ⟨a0, _, j, hj⟩ := marginal (PP a) (PP_nonneg a) (PP_sum_le a) (isNewF σN)
            (sfun σN) (sfun_le σN) (fun u => DD a u ^ (n-1))
            (fun u => pow_nonneg (DD_nonneg a u) _) (2*n) 0 k (by omega)
          calc _ ≤ ∑ x : VV n1 n2, DD a x *
                (Pop (PP a))^[j] (fun u => DD a u ^ (n-1)) x :=
                Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hj (fun _ => x))
                  (DD_nonneg a x))
            _ = ∑ x : VV n1 n2, DD a x * DD a x ^ (n-1) :=
                stat_iter (PP a) (DD a) (PP_stat a) _ j
            _ = ∑ u : VV n1 n2, DD a u ^ n := by
                apply Finset.sum_congr rfl
                intro u _
                rw [← pow_succ']
                congr 1
                omega
        calc ∑ x : VV n1 n2, DD a x * Ex (kap (PP a) (isNewF σN) (sfun σN)) (2*n) 0
              (fun _ => x) (fun h => ∏ k ∈ S, DD a (h k))
            ≤ ∑ x : VV n1 n2, DD a x * ∑ k ∈ S, c *
                Ex (kap (PP a) (isNewF σN) (sfun σN)) (2*n) 0 (fun _ => x)
                  (fun h => DD a (h k) ^ (n-1)) := by
              apply Finset.sum_le_sum
              intro x _
              apply mul_le_mul_of_nonneg_left _ (DD_nonneg a x)
              calc Ex (kap (PP a) (isNewF σN) (sfun σN)) (2*n) 0 (fun _ => x)
                    (fun h => ∏ k ∈ S, DD a (h k))
                  ≤ Ex (kap (PP a) (isNewF σN) (sfun σN)) (2*n) 0 (fun _ => x)
                    (fun h => ∑ k ∈ S, c * DD a (h k) ^ (n-1)) :=
                    Ex_mono _ hκ0 _ _ _ _ _ (fun h => amgm S (fun k => DD a (h k))
                      (fun k _ => DD_nonneg a _) (n-1) hS (by omega))
                _ = ∑ k ∈ S, Ex (kap (PP a) (isNewF σN) (sfun σN)) (2*n) 0 (fun _ => x)
                    (fun h => c * DD a (h k) ^ (n-1)) :=
                    Ex_sum _ _ _ _ S (fun k h => c * DD a (h k) ^ (n-1))
                _ = _ := Finset.sum_congr rfl (fun k _ => Ex_smul _ _ _ _ c _)
          _ = ∑ k ∈ S, c * ∑ x : VV n1 n2, DD a x *
                Ex (kap (PP a) (isNewF σN) (sfun σN)) (2*n) 0 (fun _ => x)
                  (fun h => DD a (h k) ^ (n-1)) := by
              simp only [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro k _
              apply Finset.sum_congr rfl
              intro x _
              ring
          _ ≤ ∑ k ∈ S, c * ∑ u : VV n1 n2, DD a u ^ n :=
              Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hmarg k hk)
                (by positivity))
          _ = ∑ u : VV n1 n2, DD a u ^ n := by
              rw [Finset.sum_const, hS, nsmul_eq_mul, ← mul_assoc, hc,
                mul_inv_cancel₀ (ne_of_gt hcpos), one_mul]


def σN {N : ℕ} (σ : Fin N → Fin N) : ℕ → ℕ := fun k => if hk : k < N then (σ ⟨k, hk⟩ : ℕ) else k

lemma σN_prop {N : ℕ} (σ : Fin N → Fin N) (hσ : σ ∈ PairOn (Finset.univ : Finset (Fin N))) :
    ∀ k < N, σN σ k < N ∧ σN σ k ≠ k ∧ σN σ (σN σ k) = k := by
  rw [mem_PairOn] at hσ
  intro k hk
  obtain ⟨_, h2, h3⟩ := hσ.1 ⟨k, hk⟩ (Finset.mem_univ _)
  refine ⟨?_, ?_, ?_⟩
  · simp [σN, hk]
  · simp only [σN, hk, dif_pos]
    intro h; apply h2; ext; exact h
  · simp only [σN, hk, dif_pos, (σ ⟨k, hk⟩).isLt, Fin.eta, h3]

lemma cons_iff {N : ℕ} (σ : Fin N → Fin N) (L : ℕ → Option (Fin n1 × Fin n2)) :
    (∀ k : Fin N, L (σ k) = L k) ↔ (∀ k < N, L (σN σ k) = L k) := by
  constructor
  · intro H k hk
    have := H ⟨k, hk⟩
    simpa [σN, hk] using this
  · intro H k
    have := H k.val k.isLt
    simpa [σN, k.isLt] using this

lemma rad_pointwise (N : ℕ) (h : ℕ → VV n1 n2) (I : ℝ) (hI0 : 0 ≤ I) (hI1 : I ≤ 1) :
    radE (fun ε => ∏ k ∈ Finset.range N, sgnO ε (Lh h k)) *
        (∏ k ∈ Finset.range N, AA a (h k) (h (k+1))) * I
      ≤ ∑ σ ∈ PairOn (Finset.univ : Finset (Fin N)),
          (if ∀ k < N, Lh h (σN σ k) = Lh h k then (1:ℝ) else 0) *
            ∏ k ∈ Finset.range N, AA a (h k) (h (k+1)) := by
  set W := ∏ k ∈ Finset.range N, AA a (h k) (h (k+1)) with hWdef
  have hW : ∀ σ ∈ PairOn (Finset.univ : Finset (Fin N)),
      (∀ k < N, Lh h (σN σ k) = Lh h k) → 0 ≤ W := by
    intro σ hσ hc
    rw [hWdef, prod_pair N (σN σ) (σN_prop σ hσ) (fun k => AA a (h k) (h (k+1)))]
    · exact Finset.prod_nonneg (fun k _ => sq_nonneg _)
    · intro k hk
      have := hc k hk
      unfold Lh at this
      show aO a (lab (h (σN σ k)) (h (σN σ k + 1))) = aO a (lab (h k) (h (k+1)))
      rw [this]
  have hterm : ∀ σ ∈ PairOn (Finset.univ : Finset (Fin N)),
      0 ≤ (if ∀ k < N, Lh h (σN σ k) = Lh h k then (1:ℝ) else 0) * W := by
    intro σ hσ
    split_ifs with hc
    · rw [one_mul]; exact hW σ hσ hc
    · simp
  set R := radE (fun ε => ∏ k ∈ Finset.range N, sgnO ε (Lh h k)) with hRdef
  have hR : R = radE (fun ε => ∏ k : Fin N, sgnO ε (Lh h k)) := by
    rw [hRdef]
    congr 1
    funext ε
    rw [Fin.prod_univ_eq_prod_range (fun k => sgnO ε (Lh h k)) N]
  by_cases hR0 : R = 0
  · rw [hR0, zero_mul, zero_mul]; exact Finset.sum_nonneg hterm
  · have hR0' : radE (fun ε => ∏ k : Fin N, sgnO ε (Lh h k)) ≠ 0 := by rwa [hR] at hR0
    have hev := radE_even (fun k : Fin N => Lh h k) hR0'
    obtain ⟨σ₀, hσ₀, hc₀⟩ := exists_pair (fun k : Fin N => Lh h k) N Finset.univ
      (Finset.card_fin N) (fun o => hev o)
    have hc₀' : ∀ k < N, Lh h (σN σ₀ k) = Lh h k :=
      (cons_iff σ₀ (Lh h)).mp (fun k => hc₀ k (Finset.mem_univ k))
    have hW0 := hW σ₀ hσ₀ hc₀'
    have hR1 : R ≤ 1 := by rw [hR]; exact radE_prod_le_one _
    have hRI : R * I ≤ 1 := by
      by_cases hRn : R ≤ 0
      · have : R * I ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hRn hI0
        linarith
      · push Not at hRn
        calc R * I ≤ R * 1 := mul_le_mul_of_nonneg_left hI1 (le_of_lt hRn)
          _ ≤ 1 := by rw [mul_one]; exact hR1
    calc R * W * I = W * (R * I) := by ring
      _ ≤ W * 1 := mul_le_mul_of_nonneg_left hRI hW0
      _ = (if ∀ k < N, Lh h (σN σ₀ k) = Lh h k then (1:ℝ) else 0) * W := by
          rw [if_pos hc₀']; ring
      _ ≤ _ := Finset.single_le_sum hterm hσ₀

lemma radE_sum {ι : Type} (s : Finset ι) (f : Finset (Fin n1 × Fin n2) → ι → ℝ) :
    radE (fun ε => ∑ i ∈ s, f ε i) = ∑ i ∈ s, radE (fun ε => f ε i) := by
  unfold radE
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

lemma radE_Ex (κ : ℕ → (ℕ → VV n1 n2) → VV n1 n2 → ℝ) (m T : ℕ) (h : ℕ → VV n1 n2)
    (G : Finset (Fin n1 × Fin n2) → (ℕ → VV n1 n2) → ℝ) :
    radE (fun ε => Ex κ m T h (G ε)) = Ex κ m T h (fun h' => radE (fun ε => G ε h')) := by
  unfold radE
  calc ∑ ε : Finset (Fin n1 × Fin n2), ((1:ℝ) / 2) ^ Fintype.card (Fin n1 × Fin n2) *
        Ex κ m T h (G ε)
      = ∑ ε : Finset (Fin n1 × Fin n2), Ex κ m T h
          (fun h' => ((1:ℝ) / 2) ^ Fintype.card (Fin n1 × Fin n2) * G ε h') :=
        Finset.sum_congr rfl (fun ε _ => (Ex_smul κ m T h _ (G ε)).symm)
    _ = _ := (Ex_sum κ m T h Finset.univ
          (fun ε h' => ((1:ℝ) / 2) ^ Fintype.card (Fin n1 × Fin n2) * G ε h')).symm

lemma radE_mul_const (g : Finset (Fin n1 × Fin n2) → ℝ) (c : ℝ) :
    radE (fun ε => g ε * c) = radE g * c := by
  unfold radE
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ε _
  ring

theorem main_walk (n : ℕ) (hn : 1 ≤ n)
    (H : Finset (Fin n1 × Fin n2) → Matrix (VV n1 n2) (VV n1 n2) ℝ)
    (hH : ∀ ε u v, H ε u v = sgnO ε (lab u v) * AA a u v) :
    radE (fun ε => Matrix.trace (H ε ^ (2*n))) ≤ (dfact (2*n) : ℝ) * ∑ u : VV n1 n2, DD a u ^ n := by
  set N := 2 * n with hNdef
  have step : ∀ ε, Matrix.trace (H ε ^ N) = ∑ x : VV n1 n2, Ex (fun _ _ _ => (1:ℝ)) N 0
      (fun _ => x) (fun h => (∏ k ∈ Finset.range N, sgnO ε (Lh h k)) *
        ((∏ k ∈ Finset.range N, AA a (h k) (h (k+1))) * (if h N = x then 1 else 0))) := by
    intro ε
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro x _
    have := pow_apply_Ex (H ε) N 0 (fun _ => x) x
    simp only [zero_add] at this
    rw [Matrix.diag_apply, this]
    congr 1
    funext h
    rw [← Finset.range_eq_Ico]
    simp_rw [hH]
    rw [Finset.prod_mul_distrib]
    unfold Lh
    ring
  have e : radE (fun ε => Matrix.trace (H ε ^ N)) = ∑ x : VV n1 n2, Ex (fun _ _ _ => (1:ℝ)) N 0
      (fun _ => x) (fun h => radE (fun ε => ∏ k ∈ Finset.range N, sgnO ε (Lh h k)) *
        ((∏ k ∈ Finset.range N, AA a (h k) (h (k+1))) * (if h N = x then 1 else 0))) := by
    simp_rw [step]
    rw [radE_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [radE_Ex]
    congr 1
    funext h
    exact radE_mul_const _ _
  rw [e]
  calc _ ≤ ∑ x : VV n1 n2, Ex (fun _ _ _ => (1:ℝ)) N 0 (fun _ => x)
        (fun h => ∑ σ ∈ PairOn (Finset.univ : Finset (Fin N)),
          (if ∀ k < N, Lh h (σN σ k) = Lh h k then (1:ℝ) else 0) *
            ∏ k ∈ Finset.range N, AA a (h k) (h (k+1))) := by
        apply Finset.sum_le_sum
        intro x _
        apply Ex_mono _ (fun _ _ _ => zero_le_one)
        intro h
        rw [← mul_assoc]
        apply rad_pointwise a N h
        · split_ifs <;> norm_num
        · split_ifs <;> norm_num
    _ = ∑ σ ∈ PairOn (Finset.univ : Finset (Fin N)), ∑ x : VV n1 n2,
          Ex (fun _ _ _ => (1:ℝ)) N 0 (fun _ => x)
            (fun h => (if ∀ k < N, Lh h (σN σ k) = Lh h k then (1:ℝ) else 0) *
              ∏ k ∈ Finset.range N, AA a (h k) (h (k+1))) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        exact Ex_sum _ _ _ _ _ _
    _ ≤ ∑ σ ∈ PairOn (Finset.univ : Finset (Fin N)), ∑ u : VV n1 n2, DD a u ^ n := by
        apply Finset.sum_le_sum
        intro σ hσ
        exact pair_bound a n hn (σN σ) (σN_prop σ hσ)
    _ = ((PairOn (Finset.univ : Finset (Fin N))).card : ℝ) * ∑ u : VV n1 n2, DD a u ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (dfact N : ℝ) * ∑ u : VV n1 n2, DD a u ^ n := by
        apply mul_le_mul_of_nonneg_right _
          (Finset.sum_nonneg (fun u _ => pow_nonneg (DD_nonneg a u) n))
        exact_mod_cast card_PairOn N Finset.univ (Finset.card_fin N)

end PerPair


section Final
open MatrixCompletion
open scoped Matrix

lemma toLin_pow {n2 : ℕ} (A : Matrix (Fin n2) (Fin n2) ℝ) (b : Module.Basis (Fin n2) ℝ (EuclideanSpace ℝ (Fin n2))) :
    ∀ n : ℕ, (Matrix.toLin b b A) ^ n = Matrix.toLin b b (A ^ n) := by
  intro n
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.toLin_one]; rfl
  | succ n ih => rw [pow_succ, ih, pow_succ, Matrix.toLin_mul b b b]; rfl

lemma schatten_pow {n1 n2 : ℕ} (M : Matrix (Fin n1) (Fin n2) ℝ) (n : ℕ) (hn : 1 ≤ n) :
    schattenNorm (2 * n : ℝ) M ^ (2 * n) = Matrix.trace ((Mᵀ * M) ^ n) := by
  unfold schattenNorm
  set T := Matrix.toEuclideanLin M with hT
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := finrank_euclideanSpace_fin
  have hS := T.isSymmetric_adjoint_comp_self
  have h1 : ∀ k : Fin n2, Real.rpow (T.singularValues k) (2 * n : ℝ)
      = (hS.eigenvalues hfr k) ^ n := by
    intro k
    rw [Real.rpow_eq_pow, show (2 * n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul, T.sq_singularValues_fin hfr k]
  have hnn : ∀ k : Fin n2, 0 ≤ hS.eigenvalues hfr k :=
    fun k => T.isPositive_adjoint_comp_self.nonneg_eigenvalues hfr k
  set b := hS.eigenvectorBasis hfr with hb
  have hpow : ∀ (m : ℕ) (k : Fin n2),
      ((LinearMap.adjoint T ∘ₗ T) ^ m) (b k) = (hS.eigenvalues hfr k) ^ m • b k := by
    intro m k
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hb, hS.apply_eigenvectorBasis hfr k,
        smul_smul, pow_succ]
      simp [mul_comm]
  have hsum : ∑ k : Fin n2, (hS.eigenvalues hfr k) ^ n = Matrix.trace ((Mᵀ * M) ^ n) := by
    have e1 : LinearMap.trace ℝ _ ((LinearMap.adjoint T ∘ₗ T) ^ n)
        = ∑ k : Fin n2, (hS.eigenvalues hfr k) ^ n := by
      rw [LinearMap.trace_eq_sum_inner _ b]
      apply Finset.sum_congr rfl
      intro k _
      rw [hpow n k, inner_smul_right]
      have := (orthonormal_iff_ite.mp b.orthonormal) k k
      simp only [if_true] at this
      rw [this, mul_one]
    have e2 : LinearMap.adjoint T ∘ₗ T
        = Matrix.toLin (EuclideanSpace.basisFun (Fin n2) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin n2) ℝ).toBasis (Mᵀ * M) := by
      rw [hT, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
        Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.toEuclideanLin_eq_toLin_orthonormal,
        Matrix.toLin_mul _ (EuclideanSpace.basisFun (Fin n1) ℝ).toBasis]
    rw [← e1, e2, toLin_pow, Matrix.trace_toLin_eq]
  have h2 : ∑ k : Fin n2, Real.rpow (T.singularValues k) (2 * n : ℝ)
      = ∑ k : Fin n2, (hS.eigenvalues hfr k) ^ n := Finset.sum_congr rfl (fun k _ => h1 k)
  rw [h2]
  have hpos : 0 ≤ ∑ k : Fin n2, (hS.eigenvalues hfr k) ^ n :=
    Finset.sum_nonneg (fun k _ => pow_nonneg (hnn k) n)
  rw [Real.rpow_eq_pow, show (2 * n : ℝ)⁻¹ = (((2 * n : ℕ) : ℝ))⁻¹ by push_cast; ring,
    Real.rpow_inv_natCast_pow hpos (by omega), hsum]


lemma fromBlocks_diag_pow {n1 n2 : ℕ} (A : Matrix (Fin n1) (Fin n1) ℝ) (D : Matrix (Fin n2) (Fin n2) ℝ) :
    ∀ k : ℕ, (Matrix.fromBlocks A 0 0 D) ^ k = Matrix.fromBlocks (A ^ k) 0 0 (D ^ k) := by
  intro k
  induction k with
  | zero => simp [Matrix.fromBlocks_one]
  | succ k ih => rw [pow_succ, ih, Matrix.fromBlocks_multiply, pow_succ, pow_succ]; simp

lemma trace_fromBlocks_diag {n1 n2 : ℕ} (A : Matrix (Fin n1) (Fin n1) ℝ) (D : Matrix (Fin n2) (Fin n2) ℝ) :
    Matrix.trace (Matrix.fromBlocks A 0 0 D) = Matrix.trace A + Matrix.trace D := by
  unfold Matrix.trace
  rw [Fintype.sum_sum_type]
  simp

lemma MMt_pow {n1 n2 : ℕ} (M : Matrix (Fin n1) (Fin n2) ℝ) :
    ∀ k : ℕ, (M * Mᵀ) ^ (k+1) = M * (Mᵀ * M) ^ k * Mᵀ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

lemma block_trace {n1 n2 : ℕ} (M : Matrix (Fin n1) (Fin n2) ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Matrix.trace ((Matrix.fromBlocks 0 M Mᵀ 0) ^ (2 * n)) = 2 * Matrix.trace ((Mᵀ * M) ^ n) := by
  have hsq : (Matrix.fromBlocks 0 M Mᵀ 0) ^ 2 = Matrix.fromBlocks (M * Mᵀ) 0 0 (Mᵀ * M) := by
    rw [sq, Matrix.fromBlocks_multiply]; simp
  rw [pow_mul, hsq, fromBlocks_diag_pow, trace_fromBlocks_diag]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [MMt_pow, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]
  ring

lemma gram_pow {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ℝ) (hp : 0 < p) (n : ℕ)
    (hn : 1 ≤ n) :
    (Real.rpow (∑ i : Fin m, Real.rpow (p⁻¹ * Real.sqrt (w i)) (2 * n : ℝ)) (2 * n : ℝ)⁻¹) ^ (2 * n)
      = ∑ i : Fin m, (p⁻¹ ^ 2 * w i) ^ n := by
  have h1 : ∀ i, Real.rpow (p⁻¹ * Real.sqrt (w i)) (2 * n : ℝ) = (p⁻¹ ^ 2 * w i) ^ n := by
    intro i
    rw [Real.rpow_eq_pow, show (2 * n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul, mul_pow, Real.sq_sqrt (hw i)]
  simp_rw [h1]
  have hpos : 0 ≤ ∑ i : Fin m, (p⁻¹ ^ 2 * w i) ^ n :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (mul_nonneg (by positivity) (hw i)) n)
  rw [Real.rpow_eq_pow, show (2 * n : ℝ)⁻¹ = (((2 * n : ℕ) : ℝ))⁻¹ by push_cast; ring,
    Real.rpow_inv_natCast_pow hpos (by omega)]

end Final

end AF7

set_option maxHeartbeats 4000000 in
open MatrixCompletion in
theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n))
      ≤ ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) *
          max ((sampledRowGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n))
              ((sampledColumnGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n)) := by
  set a : Fin n1 → Fin n2 → ℝ := fun i j => p⁻¹ * (if (i, j) ∈ Omega then X i j else 0) with ha
  set H : Finset (Fin n1 × Fin n2) → Matrix (AF7.VV n1 n2) (AF7.VV n1 n2) ℝ :=
    fun eps => Matrix.fromBlocks 0 (rademacherSampledMatrix Omega eps p X)
      (rademacherSampledMatrix Omega eps p X).transpose 0 with hHdef
  have hH : ∀ eps u v, H eps u v = AF7.sgnO eps (AF7.lab u v) * AF7.AA a u v := by
    intro eps u v
    rcases u with i | j <;> rcases v with i' | j'
    · simp [hHdef, AF7.lab, AF7.sgnO, AF7.AA, AF7.aO]
    · simp only [hHdef, Matrix.fromBlocks_apply₁₂, AF7.lab, AF7.sgnO, AF7.AA, AF7.aO,
        AF7.sgn, rademacherSampledMatrix, rademacherSign, ha]
      split_ifs <;> ring
    · simp only [hHdef, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply, AF7.lab, AF7.sgnO,
        AF7.AA, AF7.aO, AF7.sgn, rademacherSampledMatrix, rademacherSign, ha]
      split_ifs <;> ring
    · simp [hHdef, AF7.lab, AF7.sgnO, AF7.AA, AF7.aO]
  have hmain := AF7.main_walk a n hn H hH
  have hL : rademacherExpectation
        (fun eps => schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n))
      = AF7.radE (fun eps => Matrix.trace (H eps ^ (2 * n))) / 2 := by
    unfold AF7.radE rademacherExpectation rademacherObservationWeight
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro eps _
    beta_reduce
    rw [AF7.schatten_pow _ n hn, hHdef]
    beta_reduce
    rw [AF7.block_trace _ n hn]
    ring
  have hDl : ∀ i : Fin n1, AF7.DD a (Sum.inl i)
      = p⁻¹ ^ 2 * ∑ j : Fin n2, (if (i, j) ∈ Omega then X i j ^ 2 else 0) := by
    intro i
    unfold AF7.DD AF7.BB AF7.AA
    rw [Fintype.sum_sum_type, Finset.mul_sum]
    simp only [AF7.lab, AF7.aO, ha]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
      zero_add]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hDr : ∀ j : Fin n2, AF7.DD a (Sum.inr j)
      = p⁻¹ ^ 2 * ∑ i : Fin n1, (if (i, j) ∈ Omega then X i j ^ 2 else 0) := by
    intro j
    unfold AF7.DD AF7.BB AF7.AA
    rw [Fintype.sum_sum_type, Finset.mul_sum]
    simp only [AF7.lab, AF7.aO, ha]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
      add_zero]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hwr : ∀ i : Fin n1, 0 ≤ ∑ j : Fin n2, (if (i, j) ∈ Omega then X i j ^ 2 else 0) :=
    fun i => Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  have hwc : ∀ j : Fin n2, 0 ≤ ∑ i : Fin n1, (if (i, j) ∈ Omega then X i j ^ 2 else 0) :=
    fun j => Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)
  have hRow : (sampledRowGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n)
      = ∑ i : Fin n1, AF7.DD a (Sum.inl i) ^ n := by
    unfold sampledRowGramSchatten
    rw [AF7.gram_pow _ hwr p hp n hn]
    simp_rw [hDl]
  have hCol : (sampledColumnGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n)
      = ∑ j : Fin n2, AF7.DD a (Sum.inr j) ^ n := by
    unfold sampledColumnGramSchatten
    rw [AF7.gram_pow _ hwc p hp n hn]
    simp_rw [hDr]
  have hsplit : ∑ u : AF7.VV n1 n2, AF7.DD a u ^ n
      = ∑ i : Fin n1, AF7.DD a (Sum.inl i) ^ n + ∑ j : Fin n2, AF7.DD a (Sum.inr j) ^ n :=
    Fintype.sum_sum_type _
  have hfact : ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ)))
      = (AF7.dfact (2 * n) : ℝ) := by
    have := AF7.dfact_two_mul n
    rw [div_eq_iff (by positivity)]
    exact_mod_cast this.symm
  rw [hL, hfact, hRow, hCol]
  rw [hsplit] at hmain
  have hdf : (0:ℝ) ≤ (AF7.dfact (2 * n) : ℝ) := Nat.cast_nonneg _
  set x := ∑ i : Fin n1, AF7.DD a (Sum.inl i) ^ n
  set y := ∑ j : Fin n2, AF7.DD a (Sum.inr j) ^ n
  have hxy : (x + y) / 2 ≤ max x y := by
    rcases le_total x y with hle | hle
    · rw [max_eq_right hle]; linarith
    · rw [max_eq_left hle]; linarith
  calc AF7.radE (fun eps => Matrix.trace (H eps ^ (2 * n))) / 2
      ≤ (AF7.dfact (2 * n) : ℝ) * (x + y) / 2 := by linarith
    _ = (AF7.dfact (2 * n) : ℝ) * ((x + y) / 2) := by ring
    _ ≤ (AF7.dfact (2 * n) : ℝ) * max x y := mul_le_mul_of_nonneg_left hxy hdf
