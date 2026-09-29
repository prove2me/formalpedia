-- Prove2me | solution 2 for MarkovEntanglement.rmab_entanglement_le_configuration_deviation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T00:49:09.624294+00:00
-- url     : https://prove2.me/submissions/2185bae5-d4ba-4a8f-bbc1-f76b0e76cc83

import Mathlib
import Definitions.Def_markov_entanglement_meanfield

open scoped BigOperators
open MarkovEntanglement

namespace ME8

set_option linter.unusedSectionVars false

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ### The sup norm -/

theorem le_supNorm [Nonempty S] (v : S → ℝ) (z : S) : |v z| ≤ supNorm v :=
  le_ciSup (Finite.bddAbove_range (fun x => |v x|)) z

theorem supNorm_le [Nonempty S] {v : S → ℝ} {c : ℝ} (h : ∀ z, |v z| ≤ c) : supNorm v ≤ c :=
  ciSup_le h

theorem supNorm_nonneg [Nonempty S] (v : S → ℝ) : 0 ≤ supNorm v := by
  obtain ⟨z⟩ := ‹Nonempty S›
  exact le_trans (abs_nonneg _) (le_supNorm v z)

/-! ### The mean-field activation probability -/

theorem af_bounds (ν : S → ℝ) (β : ℝ) (m : S → ℝ) (x : S) (hm : 0 ≤ m x) :
    0 ≤ activateFraction ν β m x ∧ activateFraction ν β m x ≤ m x := by
  unfold activateFraction
  exact ⟨le_min hm (le_max_left _ _), min_le_left _ _⟩

/-- The mass in a state times its activation probability is the activated fraction. -/
theorem mass_mul_prob (ν : S → ℝ) (β : ℝ) (m : S → ℝ) (x : S) :
    m x * meanFieldActivationProb ν β m x = activateFraction ν β m x := by
  unfold meanFieldActivationProb activateFraction
  split_ifs with h
  · rw [h]
    simp
  · field_simp

theorem prob_bounds (ν : S → ℝ) (β : ℝ) (m : S → ℝ) (x : S) (hm : 0 ≤ m x) :
    0 ≤ meanFieldActivationProb ν β m x ∧ meanFieldActivationProb ν β m x ≤ 1 := by
  unfold meanFieldActivationProb
  split_ifs with h
  · norm_num
  · have hpos : 0 < m x := lt_of_le_of_ne hm (Ne.symm h)
    obtain ⟨h1, h2⟩ := af_bounds ν β m x hm
    constructor
    · exact div_nonneg h1 hm
    · rw [div_le_one hpos]
      exact h2

/-- The higher-priority mass is `(|S| - 1)`-Lipschitz: the states of strictly higher priority
than `x` never include `x` itself. -/
theorem hpm_lip [Nonempty S] (ν : S → ℝ) (m m' : S → ℝ) (x : S) :
    |higherPriorityMass ν m x - higherPriorityMass ν m' x|
      ≤ ((Fintype.card S : ℝ) - 1) * supNorm (fun z => m z - m' z) := by
  classical
  have hs := supNorm_nonneg (fun z => m z - m' z)
  have hsub : (Finset.univ.filter fun y => ν x < ν y) ⊆ Finset.univ.erase x := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ y⟩
    rintro rfl
    exact absurd hy (lt_irrefl _)
  have hcard : ((Finset.univ.filter fun y => ν x < ν y).card : ℝ) ≤ (Fintype.card S : ℝ) - 1 := by
    have h1 : (Finset.univ.filter fun y => ν x < ν y).card ≤ (Finset.univ.erase x).card :=
      Finset.card_le_card hsub
    have h2 : (Finset.univ.erase x).card = Fintype.card S - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
    have h3 : 1 ≤ Fintype.card S := Fintype.card_pos
    have h4 : (Finset.univ.filter fun y => ν x < ν y).card + 1 ≤ Fintype.card S := by omega
    have h5 : (((Finset.univ.filter fun y => ν x < ν y).card + 1 : ℕ) : ℝ)
        ≤ (Fintype.card S : ℝ) := by exact_mod_cast h4
    push_cast at h5
    linarith
  unfold higherPriorityMass
  rw [← Finset.sum_sub_distrib]
  calc |∑ y ∈ Finset.univ.filter fun y => ν x < ν y, (m y - m' y)|
      ≤ ∑ y ∈ Finset.univ.filter fun y => ν x < ν y, |m y - m' y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ Finset.univ.filter fun y => ν x < ν y, supNorm (fun z => m z - m' z) :=
        Finset.sum_le_sum fun y _ => le_supNorm (fun z => m z - m' z) y
    _ = ((Finset.univ.filter fun y => ν x < ν y).card : ℝ) * supNorm (fun z => m z - m' z) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Fintype.card S : ℝ) - 1) * supNorm (fun z => m z - m' z) :=
        mul_le_mul_of_nonneg_right hcard hs

theorem af_lip [Nonempty S] (ν : S → ℝ) (β : ℝ) (m m' : S → ℝ) (x : S)
    (hcard : 2 ≤ Fintype.card S) :
    |activateFraction ν β m x - activateFraction ν β m' x|
      ≤ ((Fintype.card S : ℝ) - 1) * supNorm (fun z => m z - m' z) := by
  have hs := supNorm_nonneg (fun z => m z - m' z)
  have hc : (2:ℝ) ≤ (Fintype.card S : ℝ) := by exact_mod_cast hcard
  unfold activateFraction
  refine le_trans (abs_min_sub_min_le_max _ _ _ _) (max_le ?_ ?_)
  · have h := le_supNorm (fun z => m z - m' z) x
    nlinarith
  · refine le_trans (abs_max_sub_max_le_max _ _ _ _) (max_le ?_ ?_)
    · simp only [sub_self, abs_zero]
      nlinarith
    · have he : (β - higherPriorityMass ν m x) - (β - higherPriorityMass ν m' x)
          = -(higherPriorityMass ν m x - higherPriorityMass ν m' x) := by ring
      rw [he, abs_neg]
      exact hpm_lip ν m m' x

/-- The occupancy-weighted deviation of the index policy's activation probability from the
mean-field limiting one is controlled by the configuration's deviation. -/
theorem prob_dev [Nonempty S] (ν : S → ℝ) (β : ℝ) (m m' : S → ℝ)
    (hm : IsConfiguration m) (hm' : IsConfiguration m') :
    ∑ x, m x * |meanFieldActivationProb ν β m x - meanFieldActivationProb ν β m' x|
      ≤ (Fintype.card S : ℝ) ^ 2 * supNorm (fun z => m z - m' z) := by
  classical
  have hs := supNorm_nonneg (fun z => m z - m' z)
  have hcpos : 1 ≤ Fintype.card S := Fintype.card_pos
  rcases Nat.lt_or_ge (Fintype.card S) 2 with hlt | hge
  · -- a single state: the two configurations coincide
    have hcard1 : Fintype.card S = 1 := by omega
    obtain ⟨x0, hx0⟩ := Fintype.card_eq_one_iff.1 hcard1
    have hmx : m = m' := by
      funext y
      have hy : y = x0 := hx0 y
      have e1 : ∑ z, m z = m x0 := by
        rw [Finset.sum_eq_single x0 (fun b _ hb => absurd (hx0 b) hb) (fun h => absurd (Finset.mem_univ x0) h)]
      have e2 : ∑ z, m' z = m' x0 := by
        rw [Finset.sum_eq_single x0 (fun b _ hb => absurd (hx0 b) hb) (fun h => absurd (Finset.mem_univ x0) h)]
      rw [hy, ← e1, ← e2, hm.2, hm'.2]
    subst hmx
    have hL : ∑ x, m x
        * |meanFieldActivationProb ν β m x - meanFieldActivationProb ν β m x| = 0 := by simp
    rw [hL]
    have hnn := supNorm_nonneg (fun z : S => m z - m z)
    have hsq : (0:ℝ) ≤ (Fintype.card S : ℝ) ^ 2 := by positivity
    exact mul_nonneg hsq hnn
  · have hterm : ∀ x : S, m x * |meanFieldActivationProb ν β m x - meanFieldActivationProb ν β m' x|
        ≤ (Fintype.card S : ℝ) * supNorm (fun z => m z - m' z) := by
      intro x
      have hmx := hm.1 x
      have hm'x := hm'.1 x
      have hdiff : m x * |meanFieldActivationProb ν β m x - meanFieldActivationProb ν β m' x|
          = |activateFraction ν β m x - m x * meanFieldActivationProb ν β m' x| := by
        rw [← abs_of_nonneg hmx, ← abs_mul, mul_sub, mass_mul_prob]
        congr 1
        rw [abs_of_nonneg hmx]
      rw [hdiff]
      by_cases hz : m' x = 0
      · have h0 : meanFieldActivationProb ν β m' x = 0 := by
          unfold meanFieldActivationProb
          rw [if_pos hz]
        rw [h0, mul_zero, sub_zero]
        obtain ⟨ha1, ha2⟩ := af_bounds ν β m x hmx
        have hx : |m x - m' x| ≤ supNorm (fun z => m z - m' z) :=
          le_supNorm (fun z => m z - m' z) x
        rw [hz, sub_zero] at hx
        rw [abs_of_nonneg ha1]
        have hc : (1:ℝ) ≤ (Fintype.card S : ℝ) := by exact_mod_cast hcpos
        have : m x ≤ supNorm (fun z => m z - m' z) := le_trans (le_abs_self _) hx
        nlinarith
      · have hpos : 0 < m' x := lt_of_le_of_ne hm'x (Ne.symm hz)
        have hprob : meanFieldActivationProb ν β m' x = activateFraction ν β m' x / m' x := by
          unfold meanFieldActivationProb
          rw [if_neg hz]
        obtain ⟨ha1, ha2⟩ := af_bounds ν β m' x hm'x
        rw [hprob]
        have h1 : |activateFraction ν β m x - m x * (activateFraction ν β m' x / m' x)|
            ≤ |activateFraction ν β m x - activateFraction ν β m' x|
              + |activateFraction ν β m' x - m x * (activateFraction ν β m' x / m' x)| :=
          abs_sub_le _ _ _
        have h2 : activateFraction ν β m' x - m x * (activateFraction ν β m' x / m' x)
            = (activateFraction ν β m' x / m' x) * (m' x - m x) := by
          field_simp
        have h3 : |activateFraction ν β m' x - m x * (activateFraction ν β m' x / m' x)|
            = (activateFraction ν β m' x / m' x) * |m' x - m x| := by
          rw [h2, abs_mul, abs_of_nonneg (div_nonneg ha1 hm'x)]
        have h4 : activateFraction ν β m' x / m' x ≤ 1 := by
          rw [div_le_one hpos]
          exact ha2
        have h5 : |m' x - m x| ≤ supNorm (fun z => m z - m' z) := by
          rw [abs_sub_comm]
          exact le_supNorm (fun z => m z - m' z) x
        have h6 := af_lip ν β m m' x hge
        have h7 : (0:ℝ) ≤ activateFraction ν β m' x / m' x := div_nonneg ha1 hm'x
        nlinarith
    calc ∑ x, m x * |meanFieldActivationProb ν β m x - meanFieldActivationProb ν β m' x|
        ≤ ∑ _x : S, (Fintype.card S : ℝ) * supNorm (fun z => m z - m' z) :=
          Finset.sum_le_sum fun x _ => hterm x
      _ = (Fintype.card S : ℝ) ^ 2 * supNorm (fun z => m z - m' z) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring

/-! ### Product sums over the joint state-action space -/

theorem prod_one' {N : ℕ} {β : Type*} [CommMonoid β] (i : Fin N) (G : Fin N → β)
    (hG : ∀ j, j ≠ i → G j = 1) : ∏ j, G j = G i :=
  Finset.prod_eq_single i (fun b _ hb => hG b hb) (fun h => absurd (Finset.mem_univ i) h)

theorem sum_prod_eq' {N : ℕ} (f : Fin N → S → ℝ) :
    ∑ s' : Fin N → S, ∏ j, f j (s' j) = ∏ j, ∑ y, f j y := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem prod_expect' {N : ℕ} (κ : Fin N → S → ℝ) (G : Fin N → S → ℝ) :
    ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * ∏ j, G j (s' j) = ∏ j, ∑ y, κ j y * G j y := by
  rw [← sum_prod_eq' (fun j y => κ j y * G j y)]
  exact Finset.sum_congr rfl fun s' _ => Finset.prod_mul_distrib.symm

theorem expect_single' {N : ℕ} (κ : Fin N → S → ℝ) (hκ : ∀ j, ∑ y, κ j y = 1)
    (i : Fin N) (g : S → ℝ) :
    ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * g (s' i) = ∑ y, κ i y * g y := by
  classical
  have h1 : ∀ s' : Fin N → S, (∏ j, (if j = i then g (s' j) else (1:ℝ))) = g (s' i) := by
    intro s'
    rw [prod_one' i _ (fun j hj => by simp only [if_neg hj]), if_pos rfl]
  calc ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * g (s' i)
      = ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * ∏ j, (if j = i then g (s' j) else (1:ℝ)) :=
        Finset.sum_congr rfl fun s' _ => by rw [h1 s']
    _ = ∏ j, ∑ y, κ j y * (if j = i then g y else (1:ℝ)) :=
        prod_expect' κ (fun j y => if j = i then g y else (1:ℝ))
    _ = ∑ y, κ i y * g y := by
        rw [prod_one' i _ (fun j hj => by simp only [if_neg hj, mul_one]; exact hκ j)]
        simp

theorem expect_const' {N : ℕ} (κ : Fin N → S → ℝ) (hκ : ∀ j, ∑ y, κ j y = 1) :
    ∑ s' : Fin N → S, ∏ j, κ j (s' j) = 1 := by
  rw [sum_prod_eq']
  simp [hκ]

theorem kernel_marginal {N : ℕ} (κ : Fin N → S → ℝ) (hκ : ∀ j, ∑ y, κ j y = 1)
    (i : Fin N) (y : S) :
    ∑ s' : Fin N → S, (if s' i = y then (∏ j, κ j (s' j)) else 0) = κ i y := by
  classical
  have h : ∀ s' : Fin N → S, (if s' i = y then (∏ j, κ j (s' j)) else 0)
      = (∏ j, κ j (s' j)) * (if s' i = y then (1:ℝ) else 0) := by
    intro s'
    by_cases hs : s' i = y <;> simp [hs]
  rw [Finset.sum_congr rfl (fun s' _ => h s'),
    expect_single' κ hκ i (fun z => if z = y then (1:ℝ) else 0)]
  simp

theorem sum_split {N : ℕ} (F : (Fin N → S × Bool) → ℝ) :
    ∑ q : Fin N → S × Bool, F q
      = ∑ s' : Fin N → S, ∑ a' : Fin N → Bool, F (fun j => (s' j, a' j)) := by
  have h1 : ∑ q : Fin N → S × Bool, F q
      = ∑ p : (Fin N → S) × (Fin N → Bool), F (fun j => (p.1 j, p.2 j)) :=
    Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => S) (fun _ => Bool)) _ _ (fun q => rfl)
  rw [h1, Fintype.sum_prod_type]

/-! ### The candidate local transition and the marginal of the induced chain -/

/-- The local transition built from an agent's own kernel and the mean-field limiting policy. -/
noncomputable def locPi (P0 P1 : Matrix S S ℝ) (ν : S → ℝ) (β : ℝ) (mstar : S → ℝ) :
    Matrix (S × Bool) (S × Bool) ℝ :=
  fun u t => rmabKernel P0 P1 u.1 u.2 t.1 * meanFieldLocalPolicy ν β mstar t.1 t.2

theorem mfLP_sum (ν : S → ℝ) (β : ℝ) (mstar : S → ℝ) (y : S) :
    ∑ b : Bool, meanFieldLocalPolicy ν β mstar y b = 1 := by
  rw [Fintype.sum_bool]
  unfold meanFieldLocalPolicy
  simp

theorem mfLP_nonneg (ν : S → ℝ) (β : ℝ) (mstar : S → ℝ) (hm : IsConfiguration mstar)
    (y : S) (b : Bool) : 0 ≤ meanFieldLocalPolicy ν β mstar y b := by
  obtain ⟨h1, h2⟩ := prob_bounds ν β mstar y (hm.1 y)
  unfold meanFieldLocalPolicy
  cases b <;> simp <;> linarith

theorem locPi_transition (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (ν : S → ℝ) (β : ℝ) (mstar : S → ℝ)
    (hm : IsConfiguration mstar) : IsTransitionMatrix (locPi P0 P1 ν β mstar) := by
  constructor
  · intro u t
    refine mul_nonneg ?_ (mfLP_nonneg ν β mstar hm t.1 t.2)
    unfold rmabKernel
    by_cases h : u.2 = true <;> simp [h, hP0.1, hP1.1]
  · intro u
    rw [Fintype.sum_prod_type]
    have h1 : ∀ y : S, ∑ b : Bool, locPi P0 P1 ν β mstar u (y, b)
        = rmabKernel P0 P1 u.1 u.2 y := by
      intro y
      unfold locPi
      dsimp only
      rw [← Finset.mul_sum, mfLP_sum, mul_one]
    rw [Finset.sum_congr rfl (fun y _ => h1 y)]
    unfold rmabKernel
    by_cases h : u.2 = true <;> simp [h, hP0.2, hP1.2]

theorem marginalN_eq {N : ℕ} (P0 P1 : Matrix S S ℝ) (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (i : Fin N) (p : Fin N → S × Bool) (y : S) (b : Bool) :
    marginalN i (inducedTransition
        (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) p (y, b)
      = ∑ s' : Fin N → S, (if s' i = y then
          (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) * policyMarginal i π s' b else 0) := by
  classical
  unfold marginalN
  rw [sum_split]
  refine Finset.sum_congr rfl fun s' _ => ?_
  by_cases h : s' i = y
  · rw [if_pos h]
    unfold policyMarginal
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    by_cases h2 : a' i = b
    · rw [if_pos (show (fun j => (s' j, a' j)) i = (y, b) by simp [h, h2]), if_pos h2]
      rfl
    · rw [if_neg (show ¬ ((fun j => (s' j, a' j)) i = (y, b)) by simp [h2]), if_neg h2, mul_zero]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun a' _ => ?_
    rw [if_neg (show ¬ ((fun j => (s' j, a' j)) i = (y, b)) by simp [h])]

/-! ### The per-state TV bound -/

theorem polMarg_sum {N : ℕ} (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπsum : ∀ st, ∑ a, π st a = 1) (i : Fin N) (s' : Fin N → S) :
    policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' true
      + policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' false = 1 := by
  classical
  unfold policyMarginal
  rw [← Finset.sum_add_distrib, ← hπsum s']
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a i = true <;> simp [h]

theorem tv_bound_p {N : ℕ} (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (ν : S → ℝ) (M : ℕ)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (hπ : IsIndexPolicy ν M π)
    (mstar : S → ℝ) (β : ℝ) (i : Fin N) (p : Fin N → S × Bool) :
    (1/2) * ∑ t : S × Bool, |marginalN i (inducedTransition
          (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) p t
        - locPi P0 P1 ν β mstar (p i) t|
      ≤ ∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) *
          |indexActivationProb ν M s' (s' i) - meanFieldActivationProb ν β mstar (s' i)| := by
  classical
  have hκnn : ∀ j y, 0 ≤ rmabKernel P0 P1 (p j).1 (p j).2 y := by
    intro j y
    unfold rmabKernel
    by_cases h : (p j).2 = true <;> simp [h, hP0.1, hP1.1]
  have hκ1 : ∀ j, ∑ y, rmabKernel P0 P1 (p j).1 (p j).2 y = 1 := by
    intro j
    unfold rmabKernel
    by_cases h : (p j).2 = true <;> simp [h, hP0.2, hP1.2]
  have hνnn : ∀ s' : Fin N → S, 0 ≤ ∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j) :=
    fun s' => Finset.prod_nonneg fun j _ => hκnn j (s' j)
  -- the difference as a single sum over `s'`
  have hdiff : ∀ (y : S) (b : Bool),
      marginalN i (inducedTransition
          (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) p (y, b)
        - locPi P0 P1 ν β mstar (p i) (y, b)
      = ∑ s' : Fin N → S, (if s' i = y then
          (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) *
            (policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' b
              - meanFieldLocalPolicy ν β mstar y b) else 0) := by
    intro y b
    rw [marginalN_eq P0 P1 π i p y b]
    have h2 : locPi P0 P1 ν β mstar (p i) (y, b)
        = ∑ s' : Fin N → S, (if s' i = y then
            (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) *
              meanFieldLocalPolicy ν β mstar y b else 0) := by
      have h3 := kernel_marginal (fun j y' => rmabKernel P0 P1 (p j).1 (p j).2 y') hκ1 i y
      unfold locPi
      dsimp only
      rw [← h3, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s' _ => ?_
      by_cases hs : s' i = y <;> simp [hs]
    rw [h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s' _ => ?_
    by_cases hs : s' i = y <;> simp [hs] <;> ring
  -- bound each coordinate
  have hb : ∀ (y : S) (b : Bool),
      |marginalN i (inducedTransition
          (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) p (y, b)
        - locPi P0 P1 ν β mstar (p i) (y, b)|
      ≤ ∑ s' : Fin N → S, (if s' i = y then
          (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) *
            |policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' b
              - meanFieldLocalPolicy ν β mstar y b| else 0) := by
    intro y b
    rw [hdiff y b]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun s' _ => ?_)
    by_cases hs : s' i = y
    · refine le_of_eq ?_
      rw [if_pos hs, if_pos hs, abs_mul, abs_of_nonneg (hνnn s')]
    · refine le_of_eq ?_
      rw [if_neg hs, if_neg hs, abs_zero]
  -- sum over the coordinates and collapse the `y` sum
  have hcol : ∀ b : Bool,
      ∑ y : S, ∑ s' : Fin N → S, (if s' i = y then
          (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) *
            |policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' b
              - meanFieldLocalPolicy ν β mstar y b| else 0)
      = ∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) *
          |policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' b
            - meanFieldLocalPolicy ν β mstar (s' i) b| := by
    intro b
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [Finset.sum_ite_eq Finset.univ (s' i) (fun y =>
      (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) *
        |policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' b
          - meanFieldLocalPolicy ν β mstar y b|)]
    simp
  -- the two Boolean coordinates give the same quantity
  have hsame : ∀ s' : Fin N → S,
      |policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' false
        - meanFieldLocalPolicy ν β mstar (s' i) false|
      = |policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' true
        - meanFieldLocalPolicy ν β mstar (s' i) true| := by
    intro s'
    have h1 := polMarg_sum π hπ.1.2 i s'
    have h2 : meanFieldLocalPolicy ν β mstar (s' i) false
        = 1 - meanFieldLocalPolicy ν β mstar (s' i) true := by
      unfold meanFieldLocalPolicy
      simp
    rw [h2]
    have h3 : policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' false
        = 1 - policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' true := by
      linarith
    rw [h3, ← abs_neg]
    congr 1
    ring
  have hpol : ∀ s' : Fin N → S,
      policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' true
        = indexActivationProb ν M s' (s' i) := fun s' => hπ.2.2 s' i
  calc (1/2) * ∑ t : S × Bool, |marginalN i (inducedTransition
          (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) p t
        - locPi P0 P1 ν β mstar (p i) t|
      = (1/2) * ∑ y : S, ∑ b : Bool, |marginalN i (inducedTransition
          (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) p (y, b)
        - locPi P0 P1 ν β mstar (p i) (y, b)| := by rw [Fintype.sum_prod_type]
    _ ≤ (1/2) * ∑ y : S, ∑ b : Bool, ∑ s' : Fin N → S, (if s' i = y then
          (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) *
            |policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' b
              - meanFieldLocalPolicy ν β mstar y b| else 0) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun b _ => hb y b
    _ = (1/2) * ∑ b : Bool, ∑ s' : Fin N → S,
          (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) *
            |policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' b
              - meanFieldLocalPolicy ν β mstar (s' i) b| := by
        rw [Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun b _ => hcol b
    _ = ∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) *
          |indexActivationProb ν M s' (s' i) - meanFieldActivationProb ν β mstar (s' i)| := by
        have hmf : ∀ x : S, meanFieldLocalPolicy ν β mstar x true
            = meanFieldActivationProb ν β mstar x := by
          intro x
          unfold meanFieldLocalPolicy
          simp
        have htrue : (∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) *
              |policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' true
                - meanFieldLocalPolicy ν β mstar (s' i) true|)
            = ∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) *
              |indexActivationProb ν M s' (s' i)
                - meanFieldActivationProb ν β mstar (s' i)| :=
          Finset.sum_congr rfl fun s' _ => by rw [hpol s', hmf (s' i)]
        have hfalse : (∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) *
              |policyMarginal (St := fun _ => S) (Act := fun _ => Bool) i π s' false
                - meanFieldLocalPolicy ν β mstar (s' i) false|)
            = ∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) *
              |indexActivationProb ν M s' (s' i)
                - meanFieldActivationProb ν β mstar (s' i)| :=
          Finset.sum_congr rfl fun s' _ => by rw [hsame s', hpol s', hmf (s' i)]
        rw [Fintype.sum_bool, htrue, hfalse]
        ring

/-! ### Stationarity and exchangeability -/

theorem stat_step {N : ℕ} (P0 P1 : Matrix S S ℝ)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (hπsum : ∀ st, ∑ a, π st a = 1)
    (μ : (Fin N → S × Bool) → ℝ)
    (hstat : IsStationary (inducedTransition
      (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) μ)
    (G : (Fin N → S) → ℝ) :
    ∑ p : Fin N → S × Bool, μ p *
        (∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) * G s')
      = ∑ q : Fin N → S × Bool, μ q * G (fun j => (q j).1) := by
  classical
  have hP : ∀ p : Fin N → S × Bool,
      ∑ q : Fin N → S × Bool, inducedTransition
          (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π p q * G (fun j => (q j).1)
        = ∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) * G s' := by
    intro p
    rw [sum_split]
    refine Finset.sum_congr rfl fun s' _ => ?_
    have h1 : ∀ a' : Fin N → Bool,
        inducedTransition (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π p
            (fun j => (s' j, a' j)) * G (fun j => ((s' j, a' j)).1)
          = ((∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) * G s') * π s' a' := by
      intro a'
      show ((∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) * π s' a') * G s' = _
      ring
    rw [Finset.sum_congr rfl (fun a' _ => h1 a'), ← Finset.mul_sum, hπsum s', mul_one]
  calc ∑ p : Fin N → S × Bool, μ p *
        (∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) * G s')
      = ∑ p : Fin N → S × Bool, μ p * ∑ q : Fin N → S × Bool, inducedTransition
          (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π p q
            * G (fun j => (q j).1) :=
        Finset.sum_congr rfl fun p _ => by rw [hP p]
    _ = ∑ q : Fin N → S × Bool, (∑ p : Fin N → S × Bool, μ p * inducedTransition
          (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π p q)
            * G (fun j => (q j).1) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by ring
    _ = ∑ q : Fin N → S × Bool, μ q * G (fun j => (q j).1) :=
        Finset.sum_congr rfl fun q _ => by rw [hstat q]

theorem stateCount_perm {N : ℕ} (s : Fin N → S) (σ : Equiv.Perm (Fin N)) (x : S) :
    stateCount (fun j => s (σ j)) x = stateCount s x := by
  classical
  unfold stateCount
  refine Finset.card_bij (fun j _ => σ j) (fun j hj => ?_) (fun j _ k _ h => ?_) (fun k hk => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hj
  · exact σ.injective h
  · refine ⟨σ.symm k, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    simpa using hk

theorem fiber_sum' {N : ℕ} (st : Fin N → S) (F : S → ℝ) :
    ∑ j, F (st j) = ∑ x, (stateCount st x : ℝ) * F x := by
  classical
  have h1 : ∀ j : Fin N, F (st j) = ∑ x, (if st j = x then F x else 0) := by
    intro j
    rw [Finset.sum_ite_eq Finset.univ (st j) F]
    simp
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

theorem sum_stateCount {N : ℕ} (st : Fin N → S) : ∑ x, stateCount st x = N := by
  classical
  unfold stateCount
  rw [← Finset.card_eq_sum_card_fiberwise (f := st) (t := (Finset.univ : Finset S))
    (fun j _ => Finset.mem_univ (st j)), Finset.card_univ, Fintype.card_fin]

theorem configuration_isConfig {N : ℕ} (hN : 0 < N) (st : Fin N → S) :
    IsConfiguration (configuration st) := by
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  constructor
  · intro x
    unfold configuration
    positivity
  · unfold configuration
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_stateCount]
    field_simp

theorem exch_step {N : ℕ} (hN : 0 < N) (μ : (Fin N → S × Bool) → ℝ)
    (hexch : IsExchangeableDist μ) (i : Fin N) (F : (S → ℝ) → S → ℝ) :
    ∑ q : Fin N → S × Bool, μ q * F (configuration (fun j => (q j).1)) ((q i).1)
      = ∑ q : Fin N → S × Bool, μ q *
          ∑ x, configuration (fun j => (q j).1) x * F (configuration (fun j => (q j).1)) x := by
  classical
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hj : ∀ j : Fin N,
      ∑ q : Fin N → S × Bool, μ q * F (configuration (fun l => (q l).1)) ((q j).1)
        = ∑ q : Fin N → S × Bool, μ q * F (configuration (fun l => (q l).1)) ((q i).1) := by
    intro j
    have hσ : (Equiv.swap i j) j = i := by simp
    let e : (Fin N → S × Bool) ≃ (Fin N → S × Bool) :=
      { toFun := fun q l => q ((Equiv.swap i j) l)
        invFun := fun q l => q ((Equiv.swap i j).symm l)
        left_inv := fun q => by funext l; simp
        right_inv := fun q => by funext l; simp }
    have key : ∀ q : Fin N → S × Bool,
        μ (fun l => q ((Equiv.swap i j) l))
            * F (configuration (fun l => (q ((Equiv.swap i j) l)).1))
              ((q ((Equiv.swap i j) j)).1)
          = μ q * F (configuration (fun l => (q l).1)) ((q i).1) := by
      intro q
      have h1 : μ (fun l => q ((Equiv.swap i j) l)) = μ q := hexch (Equiv.swap i j) q
      have h2 : configuration (fun l => (q ((Equiv.swap i j) l)).1)
          = configuration (fun l => (q l).1) := by
        funext x
        unfold configuration
        rw [stateCount_perm (fun l => (q l).1) (Equiv.swap i j) x]
      rw [h1, h2, hσ]
    calc ∑ q : Fin N → S × Bool, μ q * F (configuration (fun l => (q l).1)) ((q j).1)
        = ∑ q : Fin N → S × Bool, μ (fun l => q ((Equiv.swap i j) l))
            * F (configuration (fun l => (q ((Equiv.swap i j) l)).1))
              ((q ((Equiv.swap i j) j)).1) :=
          (Fintype.sum_equiv e
            (fun q => μ (fun l => q ((Equiv.swap i j) l))
              * F (configuration (fun l => (q ((Equiv.swap i j) l)).1))
                ((q ((Equiv.swap i j) j)).1))
            (fun q => μ q * F (configuration (fun l => (q l).1)) ((q j).1))
            (fun q => rfl)).symm
      _ = ∑ q : Fin N → S × Bool, μ q * F (configuration (fun l => (q l).1)) ((q i).1) :=
          Finset.sum_congr rfl fun q _ => key q
  have hB : ∀ q : Fin N → S × Bool,
      ∑ x, configuration (fun l => (q l).1) x * F (configuration (fun l => (q l).1)) x
        = (1/(N:ℝ)) * ∑ j : Fin N, F (configuration (fun l => (q l).1)) ((q j).1) := by
    intro q
    rw [fiber_sum' (fun l => (q l).1) (F (configuration (fun l => (q l).1))), Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold configuration
    ring
  calc ∑ q : Fin N → S × Bool, μ q * F (configuration (fun l => (q l).1)) ((q i).1)
      = (1/(N:ℝ)) * ∑ _j : Fin N,
          ∑ q : Fin N → S × Bool, μ q * F (configuration (fun l => (q l).1)) ((q i).1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
    _ = (1/(N:ℝ)) * ∑ j : Fin N,
          ∑ q : Fin N → S × Bool, μ q * F (configuration (fun l => (q l).1)) ((q j).1) := by
        congr 1
        exact Finset.sum_congr rfl fun j _ => (hj j).symm
    _ = ∑ q : Fin N → S × Bool, μ q *
          ((1/(N:ℝ)) * ∑ j : Fin N, F (configuration (fun l => (q l).1)) ((q j).1)) := by
        have h1 : ∀ j : Fin N, (1/(N:ℝ)) * ∑ q : Fin N → S × Bool,
              μ q * F (configuration (fun l => (q l).1)) ((q j).1)
            = ∑ q : Fin N → S × Bool,
              (1/(N:ℝ)) * (μ q * F (configuration (fun l => (q l).1)) ((q j).1)) :=
          fun j => Finset.mul_sum _ _ _
        rw [Finset.mul_sum, Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => h1 j),
          Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        have h2 : μ q * ((1/(N:ℝ)) * ∑ j : Fin N, F (configuration (fun l => (q l).1)) ((q j).1))
            = ∑ j : Fin N, (1/(N:ℝ)) * (μ q * F (configuration (fun l => (q l).1)) ((q j).1)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [h2]
    _ = ∑ q : Fin N → S × Bool, μ q *
          ∑ x, configuration (fun l => (q l).1) x * F (configuration (fun l => (q l).1)) x :=
        Finset.sum_congr rfl fun q _ => by rw [hB q]

/-! ### Identifying the index policy's activation probability -/

theorem hpm_eq' {N : ℕ} (ν : S → ℝ) (st : Fin N → S) (x : S) :
    higherPriorityMass ν (configuration st) x = (higherPriorityCount ν st x : ℝ) / (N : ℝ) := by
  unfold higherPriorityMass higherPriorityCount configuration
  rw [Nat.cast_sum, Finset.sum_div]

theorem activateFraction_eq' {N : ℕ} (ν : S → ℝ) (M : ℕ) (hN : 0 < N) (st : Fin N → S) (x : S) :
    activateFraction ν ((M : ℝ) / (N : ℝ)) (configuration st) x
      = (activateCount ν M st x : ℝ) / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  unfold activateFraction
  rw [hpm_eq', div_sub_div_same]
  unfold configuration activateCount
  rcases le_total (higherPriorityCount ν st x) M with hle | hge
  · have h1 : (0 : ℝ) ≤ ((M : ℝ) - (higherPriorityCount ν st x : ℝ)) / (N : ℝ) := by
      have : ((higherPriorityCount ν st x : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hle
      positivity
    rw [max_eq_right h1, min_div_div_right hNpos.le]
    congr 1
    rw [Nat.cast_min, Nat.cast_sub hle]
  · have h0 : M - higherPriorityCount ν st x = 0 := Nat.sub_eq_zero_of_le hge
    have h1 : ((M : ℝ) - (higherPriorityCount ν st x : ℝ)) / (N : ℝ) ≤ 0 := by
      have : (M : ℝ) ≤ (higherPriorityCount ν st x : ℝ) := by exact_mod_cast hge
      apply div_nonpos_of_nonpos_of_nonneg <;> linarith
    rw [max_eq_left h1, h0]
    simp
    positivity

theorem index_prob_eq {N : ℕ} (ν : S → ℝ) (M : ℕ) (hN : 0 < N) (st : Fin N → S) (x : S) :
    indexActivationProb ν M st x
      = meanFieldActivationProb ν ((M:ℝ)/(N:ℝ)) (configuration st) x := by
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hcfg : configuration st x = (stateCount st x : ℝ) / (N : ℝ) := rfl
  unfold indexActivationProb meanFieldActivationProb
  rw [activateFraction_eq' ν M hN st x]
  by_cases h : stateCount st x = 0
  · rw [if_pos h, if_pos (show configuration st x = 0 by rw [hcfg, h]; simp)]
  · have hs : ((stateCount st x : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 h
    have h2 : configuration st x ≠ 0 := by
      rw [hcfg]
      exact div_ne_zero hs (ne_of_gt hNR)
    rw [if_neg h, if_neg h2, hcfg]
    field_simp

end ME8

open MarkovEntanglement ME8 in
theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (hν : Function.Injective ν) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (mstar : S → ℝ) (hmstar : IsConfiguration mstar)
    (N : ℕ) (hN : 0 < N)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπ : IsIndexPolicy ν ⌊α * (N : ℝ)⌋₊ π)
    (μ : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)) → ℝ)
    (hμ : IsDist μ) (hexch : IsExchangeableDist μ)
    (hstat : IsStationary (inducedTransition
      (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) μ)
    (i : Fin N) :
    entanglementN i μ (inducedTransition
        (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π)
      ≤ (Fintype.card S : ℝ) ^ 2 *
          ∑ p : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)),
            μ p * supNorm (fun x => configuration (fun j => (p j).1) x - mstar x) := by
  classical
  haveI hSne : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := hmstar.2
    simp at h1
  set M : ℕ := ⌊α * (N : ℝ)⌋₊ with hM
  set β : ℝ := (M:ℝ)/(N:ℝ) with hβ
  -- the entanglement is at most the deviation from the mean-field limiting local transition
  have hle : entanglementN i μ (inducedTransition
        (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π)
      ≤ muAgentTVDistN i μ (inducedTransition
        (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π)
        (ME8.locPi P0 P1 ν β mstar) := by
    unfold entanglementN
    refine csInf_le ⟨0, ?_⟩ ⟨ME8.locPi P0 P1 ν β mstar,
      ME8.locPi_transition P0 P1 hP0 hP1 ν β mstar hmstar, rfl⟩
    rintro r ⟨Pi, -, rfl⟩
    unfold muAgentTVDistN
    exact Finset.sum_nonneg fun p _ => mul_nonneg (hμ.1 p) (by positivity)
  refine le_trans hle ?_
  -- bound each row by the deviation of the activation probability
  have hstep2 : muAgentTVDistN i μ (inducedTransition
        (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π)
        (ME8.locPi P0 P1 ν β mstar)
      ≤ ∑ p : Fin N → S × Bool, μ p *
          (∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (p j).1 (p j).2 (s' j)) *
            |indexActivationProb ν M s' (s' i)
              - meanFieldActivationProb ν β mstar (s' i)|) := by
    unfold muAgentTVDistN
    exact Finset.sum_le_sum fun p _ =>
      mul_le_mul_of_nonneg_left
        (ME8.tv_bound_p P0 P1 hP0 hP1 ν M π hπ mstar β i p) (hμ.1 p)
  refine le_trans hstep2 ?_
  -- stationarity moves the expectation back to `μ`
  rw [ME8.stat_step P0 P1 π hπ.1.2 μ hstat
    (fun s' => |indexActivationProb ν M s' (s' i)
      - meanFieldActivationProb ν β mstar (s' i)|)]
  -- the index policy's probability is the mean-field one at the current configuration
  have hrw : ∀ q : Fin N → S × Bool,
      μ q * |indexActivationProb ν M (fun j => (q j).1) ((q i).1)
        - meanFieldActivationProb ν β mstar ((q i).1)|
      = μ q * (fun m x => |meanFieldActivationProb ν β m x
          - meanFieldActivationProb ν β mstar x|)
          (configuration (fun j => (q j).1)) ((q i).1) := by
    intro q
    rw [index_prob_eq ν M hN (fun j => (q j).1) ((q i).1)]
  rw [Finset.sum_congr rfl (fun q (_ : q ∈ Finset.univ) => hrw q),
    ME8.exch_step hN μ hexch i (fun m x => |meanFieldActivationProb ν β m x
      - meanFieldActivationProb ν β mstar x|), Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  have hpd := ME8.prob_dev ν β (configuration (fun j => (q j).1)) mstar
    (ME8.configuration_isConfig hN _) hmstar
  have hmul := mul_le_mul_of_nonneg_left hpd (hμ.1 q)
  nlinarith [hmul]
