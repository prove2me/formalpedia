-- Prove2me | solution 1 for MarkovMixing.resistance_triangle
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T16:18:25.086306+00:00
-- url     : https://prove2.me/submissions/fad36d81-71ec-451a-96e1-d99a2d1ad423

import Theorems.Thm_MarkovMixing_summable_hitting_tails
import Theorems.Thm_MarkovMixing_stationary_unique
import Theorems.Thm_MarkovMixing_exists_stationary_pos
import Theorems.Thm_MarkovMixing_harmonic_extension
import Theorems.Thm_MarkovMixing_commute_time_identity
import Definitions.Def_mm_network
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped BigOperators
open MarkovMixing

set_option maxRecDepth 8000
open MarkovMixing

set_option maxRecDepth 8000

/-- The chain `P` killed on entering `z`. -/
private def killed {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (z : V) : Matrix V V ℝ :=
  fun a b => if b = z then 0 else P a b

/-- Splitting a trajectory of length `n+1` into its first `n` steps and its final state. -/
private def snocEquivV (V : Type*) (n : ℕ) : ((Fin (n + 1) → V) × V) ≃ (Fin (n + 2) → V) where
  toFun p := Fin.snoc p.1 p.2
  invFun ω := (fun i => ω i.castSucc, ω (Fin.last (n + 1)))
  left_inv := by rintro ⟨q, v⟩; ext <;> simp
  right_inv := by intro ω; exact Fin.snoc_init_self ω

@[simp] private lemma snocEquivV_castSucc {V : Type*} (n : ℕ)
    (p : (Fin (n + 1) → V) × V) (i : Fin (n + 1)) :
    snocEquivV V n p i.castSucc = p.1 i := by
  simp [snocEquivV]

@[simp] private lemma snocEquivV_last {V : Type*} (n : ℕ) (p : (Fin (n + 1) → V) × V) :
    snocEquivV V n p (Fin.last (n + 1)) = p.2 := by
  simp [snocEquivV]


/-- The endpoint-refined path sum is an entry of a power of the killed chain. -/
private lemma avoidHit_eq_killed_pow {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (z : V) :
    ∀ (t : ℕ) (a y : V), avoidHitProb P a z y t = ((killed P z) ^ t) a y := by
  classical
  set M := killed P z with hMdef
  have hMval : ∀ a b : V, M a b = if b = z then 0 else P a b := fun a b => rfl
  have hMz : ∀ a : V, M a z = 0 := fun a => by rw [hMval]; simp
  -- (A) the endpoint-refined path sum is a matrix entry of the killed chain
  have hkeyH : ∀ (t : ℕ) (a y : V), avoidHitProb P a z y t = (M ^ t) a y := by
    intro t
    induction t with
    | zero =>
        intro a y
        have hL : avoidHitProb P a z y 0
            = ∑ ω : Fin 1 → V, (if ω 0 = a ∧ ω 0 = y then (1:ℝ) else 0) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          have hcond : (ω 0 = a ∧ (∀ i : Fin 1, i ≠ 0 → ω i ≠ z) ∧ ω (Fin.last 0) = y)
              ↔ (ω 0 = a ∧ ω 0 = y) := by
            constructor
            · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
            · rintro ⟨h1, h2⟩
              exact ⟨h1, fun i hi => absurd (Subsingleton.elim i 0) hi, h2⟩
          by_cases h : ω 0 = a ∧ ω 0 = y
          · rw [if_pos (hcond.mpr h), if_pos h]
            simp [pathWeight]
          · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
        rw [hL, Fintype.sum_equiv (Equiv.funUnique (Fin 1) V)
          (fun ω : Fin 1 → V => if ω 0 = a ∧ ω 0 = y then (1:ℝ) else 0)
          (fun v : V => if v = a ∧ v = y then (1:ℝ) else 0) (fun ω => rfl)]
        rw [pow_zero, Matrix.one_apply]
        by_cases hay : a = y
        · subst hay
          rw [if_pos rfl]
          rw [Finset.sum_eq_single a]
          · rw [if_pos ⟨rfl, rfl⟩]
          · intro b _ hb; rw [if_neg (fun hc => hb hc.1)]
          · intro hc; exact absurd (Finset.mem_univ a) hc
        · rw [if_neg hay]
          refine Finset.sum_eq_zero fun v _ => ?_
          rw [if_neg]
          rintro ⟨h1, h2⟩
          exact hay (h1.symm.trans h2)
    | succ n ih =>
        intro a y
        have hunfold : avoidHitProb P a z y (n + 1)
            = ∑ ω : Fin (n + 2) → V,
                (if ω 0 = a ∧ (∀ i : Fin (n + 2), i ≠ 0 → ω i ≠ z) ∧
                    ω (Fin.last (n + 1)) = y then pathWeight P ω else 0) := rfl
        rw [hunfold, ← Equiv.sum_comp (snocEquivV V n)
          (fun ω : Fin (n + 2) → V =>
            if ω 0 = a ∧ (∀ i : Fin (n + 2), i ≠ 0 → ω i ≠ z) ∧
                ω (Fin.last (n + 1)) = y then pathWeight P ω else 0)]
        have hstep : ∀ p : (Fin (n + 1) → V) × V,
            (if (snocEquivV V n p) 0 = a ∧
                (∀ i : Fin (n + 2), i ≠ 0 → (snocEquivV V n p) i ≠ z) ∧
                (snocEquivV V n p) (Fin.last (n + 1)) = y then
              pathWeight P (snocEquivV V n p) else 0)
            = (if (p.1 0 = a ∧ ∀ i : Fin (n + 1), i ≠ 0 → p.1 i ≠ z) ∧ (p.2 ≠ z ∧ p.2 = y) then
                pathWeight P p.1 * P (p.1 (Fin.last n)) p.2 else 0) := by
          intro p
          have hrestrict : ∀ i : Fin (n + 1), (snocEquivV V n p) i.castSucc = p.1 i :=
            fun i => snocEquivV_castSucc n p i
          have hlast : (snocEquivV V n p) (Fin.last (n + 1)) = p.2 := snocEquivV_last n p
          have hzero : (snocEquivV V n p) 0 = p.1 0 := by
            have h := hrestrict 0
            rwa [Fin.castSucc_zero] at h
          have hcond : ((snocEquivV V n p) 0 = a ∧
                (∀ i : Fin (n + 2), i ≠ 0 → (snocEquivV V n p) i ≠ z) ∧
                (snocEquivV V n p) (Fin.last (n + 1)) = y)
              ↔ ((p.1 0 = a ∧ ∀ i : Fin (n + 1), i ≠ 0 → p.1 i ≠ z) ∧ (p.2 ≠ z ∧ p.2 = y)) := by
            constructor
            · rintro ⟨h0, hne, hy⟩
              refine ⟨⟨hzero ▸ h0, fun i hi => ?_⟩, ?_, hlast ▸ hy⟩
              · rw [← hrestrict i]
                refine hne i.castSucc ?_
                intro hc
                exact hi (Fin.ext (by
                  have : (i.castSucc : ℕ) = 0 := by rw [hc]; rfl
                  simpa using this))
              · rw [← hlast]
                refine hne _ ?_
                intro hc
                have : ((Fin.last (n + 1)) : ℕ) = 0 := by rw [hc]; rfl
                simp at this
            · rintro ⟨⟨h0, hne⟩, hlz, hy⟩
              refine ⟨hzero ▸ h0, fun i hi => ?_, hlast ▸ hy⟩
              induction i using Fin.lastCases with
              | last => rw [hlast]; exact hlz
              | cast j =>
                  rw [hrestrict j]
                  refine hne j ?_
                  intro hc
                  exact hi (by subst hc; rw [Fin.castSucc_zero])
          have hweight : pathWeight P (snocEquivV V n p)
              = pathWeight P p.1 * P (p.1 (Fin.last n)) p.2 := by
            have hpw : pathWeight P (snocEquivV V n p)
                = ∏ i : Fin (n + 1),
                    P ((snocEquivV V n p) i.castSucc) ((snocEquivV V n p) i.succ) := rfl
            rw [hpw, Fin.prod_univ_castSucc]
            congr 1
            · refine Finset.prod_congr rfl fun i _ => ?_
              rw [hrestrict i.castSucc]
              congr 1
              exact hrestrict i.succ
            · rw [hrestrict (Fin.last n)]
              congr 1
          by_cases h : (p.1 0 = a ∧ ∀ i : Fin (n + 1), i ≠ 0 → p.1 i ≠ z) ∧ (p.2 ≠ z ∧ p.2 = y)
          · rw [if_pos (hcond.mpr h), if_pos h, hweight]
          · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
        rw [Finset.sum_congr rfl fun p _ => hstep p, Fintype.sum_prod_type]
        -- collapse the inner sum over the final state
        have hinner : ∀ ω : Fin (n + 1) → V,
            (∑ v : V, if (ω 0 = a ∧ ∀ i : Fin (n + 1), i ≠ 0 → ω i ≠ z) ∧ (v ≠ z ∧ v = y) then
                pathWeight P ω * P (ω (Fin.last n)) v else 0)
            = (if ω 0 = a ∧ ∀ i : Fin (n + 1), i ≠ 0 → ω i ≠ z then
                pathWeight P ω * M (ω (Fin.last n)) y else 0) := by
          intro ω
          by_cases h : ω 0 = a ∧ ∀ i : Fin (n + 1), i ≠ 0 → ω i ≠ z
          · rw [if_pos h]
            by_cases hyz : y = z
            · rw [hyz, hMz, mul_zero]
              refine Finset.sum_eq_zero fun v _ => ?_
              rw [if_neg]
              rintro ⟨-, hvz, hvy⟩
              exact hvz hvy
            · rw [Finset.sum_eq_single y]
              · rw [if_pos ⟨h, hyz, rfl⟩, hMval, if_neg hyz]
              · intro v _ hv
                rw [if_neg]
                rintro ⟨-, -, hvy⟩
                exact hv hvy
              · intro hc; exact absurd (Finset.mem_univ y) hc
          · rw [if_neg h]
            exact Finset.sum_eq_zero fun v _ => by rw [if_neg (fun hc => h hc.1)]
        rw [Finset.sum_congr rfl fun ω _ => hinner ω]
        -- and recognise the result as an entry of `M ^ (n+1)`
        rw [pow_succ]
        have hrhs : (M ^ n * M) a y = ∑ w, (M ^ n) a w * M w y := rfl
        rw [hrhs]
        have hexp : ∀ w : V, (M ^ n) a w * M w y
            = ∑ ω : Fin (n + 1) → V,
                (if (ω 0 = a ∧ (∀ i : Fin (n + 1), i ≠ 0 → ω i ≠ z) ∧ ω (Fin.last n) = w) then
                  pathWeight P ω * M w y else 0) := by
          intro w
          rw [← ih a w]
          have : avoidHitProb P a z w n
              = ∑ ω : Fin (n + 1) → V,
                  (if (ω 0 = a ∧ (∀ i : Fin (n + 1), i ≠ 0 → ω i ≠ z) ∧
                      ω (Fin.last n) = w) then pathWeight P ω else 0) := rfl
          rw [this, Finset.sum_mul]
          refine Finset.sum_congr rfl fun ω _ => ?_
          by_cases h : ω 0 = a ∧ (∀ i : Fin (n + 1), i ≠ 0 → ω i ≠ z) ∧ ω (Fin.last n) = w
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h, zero_mul]
        rw [Finset.sum_congr rfl fun w _ => hexp w, Finset.sum_comm]
        refine Finset.sum_congr rfl fun ω _ => ?_
        by_cases h : ω 0 = a ∧ ∀ i : Fin (n + 1), i ≠ 0 → ω i ≠ z
        · rw [if_pos h, Finset.sum_eq_single (ω (Fin.last n))]
          · rw [if_pos ⟨h.1, h.2, rfl⟩]
          · intro w _ hw
            rw [if_neg]
            rintro ⟨-, -, hlw⟩
            exact hw hlw.symm
          · intro hc; exact absurd (Finset.mem_univ _) hc
        · rw [if_neg h]
          exact (Finset.sum_eq_zero fun w _ => by
            rw [if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]).symm
  exact hkeyH

/-- The avoidance tail probability is the corresponding row sum of the killed chain. -/
private lemma avoidTail_eq_rowSum {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (z : V) :
    ∀ (t : ℕ) (a : V), avoidTailProb P a z t = ∑ y, ((killed P z) ^ t) a y := by
  classical
  set M := killed P z with hMdef
  have hkeyH : ∀ (t : ℕ) (a y : V), avoidHitProb P a z y t = (M ^ t) a y :=
    avoidHit_eq_killed_pow P z
  -- (B) the tail probability is the corresponding row sum
  have hkeyT : ∀ (t : ℕ) (a : V), avoidTailProb P a z t = ∑ y, (M ^ t) a y := by
    intro t a
    have hsum : ∑ y, (M ^ t) a y = ∑ y, avoidHitProb P a z y t :=
      Finset.sum_congr rfl fun y _ => (hkeyH t a y).symm
    rw [hsum]
    have hexp : ∀ y : V, avoidHitProb P a z y t
        = ∑ ω : Fin (t + 1) → V,
            (if (ω 0 = a ∧ (∀ i : Fin (t + 1), i ≠ 0 → ω i ≠ z) ∧ ω (Fin.last t) = y) then
              pathWeight P ω else 0) := fun y => rfl
    rw [Finset.sum_congr rfl fun y _ => hexp y, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h : ω 0 = a ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ≠ z
    · rw [if_pos h, Finset.sum_eq_single (ω (Fin.last t))]
      · rw [if_pos ⟨h.1, h.2, rfl⟩]
      · intro y _ hy
        rw [if_neg]
        rintro ⟨-, -, hly⟩
        exact hy hly.symm
      · intro hc; exact absurd (Finset.mem_univ _) hc
    · rw [if_neg h]
      exact (Finset.sum_eq_zero fun y _ => by
        rw [if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]).symm
  exact hkeyT


/-! ### The random target lemma -/

/-- The expected hitting time of a singleton, in terms of the first-return functional. -/
private lemma setHit_eq {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) :
    ∀ x y : V, expSetHitTime P x {y} = if x = y then 0 else expHitTimePos P x y := by
  classical
  have hSA : ∀ (x y : V) (t : ℕ),
      setAvoidTailProb P x {y} t = if x = y then 0 else avoidTailProb P x y t := by
    intro x y t
    by_cases hxy : x = y
    · rw [if_pos hxy]
      refine Finset.sum_eq_zero fun ω _ => ?_
      rw [if_neg]
      rintro ⟨h0, hall⟩
      exact hall 0 (by rw [h0, hxy]; exact Finset.mem_singleton_self y)
    · rw [if_neg hxy]
      refine Finset.sum_congr rfl fun ω _ => ?_
      have hiff : (ω 0 = x ∧ ∀ i : Fin (t + 1), ω i ∉ ({y} : Finset V))
          ↔ (ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ≠ y) := by
        constructor
        · rintro ⟨h0, hall⟩
          exact ⟨h0, fun i _ hi => hall i (by rw [hi]; exact Finset.mem_singleton_self y)⟩
        · rintro ⟨h0, hall⟩
          refine ⟨h0, fun i hi => ?_⟩
          rw [Finset.mem_singleton] at hi
          by_cases hi0 : i = 0
          · rw [hi0] at hi; rw [h0] at hi; exact hxy hi
          · exact hall i hi0 hi
      by_cases hc : ω 0 = x ∧ ∀ i : Fin (t + 1), ω i ∉ ({y} : Finset V)
      · rw [if_pos hc, if_pos (hiff.mp hc)]
      · rw [if_neg hc, if_neg (fun hd => hc (hiff.mpr hd))]
  have hexpS : ∀ x y : V,
      expSetHitTime P x {y} = if x = y then 0 else expHitTimePos P x y := by
    intro x y
    unfold expSetHitTime expHitTimePos
    by_cases hxy : x = y
    · rw [if_pos hxy]
      rw [tsum_congr fun t => hSA x y t]
      simp [hxy]
    · rw [if_neg hxy]
      exact tsum_congr fun t => by rw [hSA x y t, if_neg hxy]
  exact hexpS

/-- The one-step recursion for expected first-return times. -/
private lemma hitTime_rec {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P) :
    ∀ x y : V, expHitTimePos P x y = 1 + ∑ z, (killed P y) x z * expHitTimePos P z y := by
  classical
  have hA0 : ∀ x y : V, avoidTailProb P x y 0 = 1 := by
    intro x y
    unfold avoidTailProb
    have hw : ∀ ω : Fin 1 → V, pathWeight P ω = 1 := by
      intro ω; simp [pathWeight]
    have hterm : ∀ ω : Fin 1 → V,
        (if ω 0 = x ∧ (∀ i : Fin 1, i ≠ 0 → ω i ≠ y) then pathWeight P ω else 0)
          = if ω 0 = x then (1 : ℝ) else 0 := by
      intro ω
      have hvac : (∀ i : Fin 1, i ≠ 0 → ω i ≠ y) := by
        intro i hi
        exact absurd (Subsingleton.elim i 0) hi
      by_cases h : ω 0 = x
      · rw [if_pos ⟨h, hvac⟩, if_pos h, hw]
      · rw [if_neg (fun hc => h hc.1), if_neg h]
    rw [Finset.sum_congr rfl fun ω _ => hterm ω]
    rw [Finset.sum_eq_single (fun _ : Fin 1 => x)]
    · simp
    · intro ω _ hne
      rw [if_neg]
      intro h0
      exact hne (funext fun i => by rw [Subsingleton.elim i 0, h0])
    · intro hc; exact absurd (Finset.mem_univ _) hc
  -- (2) the one-step recursion, read off the killed chain
  have hArec : ∀ (y : V) (t : ℕ) (x : V),
      avoidTailProb P x y (t + 1) = ∑ z, (killed P y) x z * avoidTailProb P z y t := by
    intro y t x
    rw [avoidTail_eq_rowSum P y (t + 1) x]
    have hpow : ∀ w : V, ((killed P y) ^ (t + 1)) x w
        = ∑ z, (killed P y) x z * ((killed P y) ^ t) z w := by
      intro w
      rw [pow_succ']
      exact Matrix.mul_apply
    rw [Finset.sum_congr rfl fun w _ => hpow w, Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [avoidTail_eq_rowSum P y t z, Finset.mul_sum]
  have hsummable : ∀ x y : V, Summable (fun t : ℕ => avoidTailProb P x y t) :=
    fun x y => MarkovMixing.summable_hitting_tails P hP hirr x y
  have hrec : ∀ x y : V,
      expHitTimePos P x y = 1 + ∑ z, (killed P y) x z * expHitTimePos P z y := by
    intro x y
    unfold expHitTimePos
    rw [(hsummable x y).tsum_eq_zero_add, hA0 x y]
    congr 1
    rw [tsum_congr fun t => hArec y t x]
    rw [Summable.tsum_finsetSum (fun z _ => (hsummable z y).mul_left _)]
    exact Finset.sum_congr rfl fun z _ => tsum_mul_left
  exact hrec

/-- Nonnegativity of the set-avoidance tail probabilities. -/
private lemma setAvoidTail_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (x : V) (S : Finset V) (t : ℕ) :
    0 ≤ setAvoidTailProb P x S t := by
  refine Finset.sum_nonneg fun ω _ => ?_
  split
  · exact Finset.prod_nonneg fun i _ => hP.1 _ _
  · exact le_refl 0

private lemma hitSetAt_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (x : V) (B : Finset V) (y : V) (t : ℕ) :
    0 ≤ hitSetAtProb P x B y t := by
  refine Finset.sum_nonneg fun ω _ => ?_
  split
  · exact Finset.prod_nonneg fun i _ => hP.1 _ _
  · exact le_refl 0

/-- The expected hitting time of a set is nonnegative. -/
private lemma expSetHitTime_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (x : V) (S : Finset V) :
    0 ≤ expSetHitTime P x S :=
  tsum_nonneg fun t => setAvoidTail_nonneg P hP x S t

private lemma firstHitAt_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (x : V) (B : Finset V) (y : V) :
    0 ≤ firstHitAtProb P x B y :=
  tsum_nonneg fun t => hitSetAt_nonneg P hP x B y t

/-- The triangle inequality for expected hitting times. -/
private lemma hitTime_triangle {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (y z : V) (hyz : y ≠ z) (x : V) :
    expSetHitTime P x {z} ≤ expSetHitTime P x {y} + expSetHitTime P y {z} := by
  classical
  haveI : Nonempty V := ⟨x⟩
  have hstepsum : ∀ (u v : V), ∑ w, P u w * expSetHitTime P w {v}
      = expHitTimePos P u v - 1 := by
    intro u v
    have h1 : ∀ w : V,
        P u w * expSetHitTime P w {v} = (killed P v) u w * expHitTimePos P w v := by
      intro w
      rw [setHit_eq P w v]
      by_cases hwv : w = v
      · rw [if_pos hwv, show (killed P v) u w = 0 from by simp [killed, hwv]]; ring
      · rw [if_neg hwv, show (killed P v) u w = P u w from by simp [killed, hwv]]
    rw [Finset.sum_congr rfl fun w _ => h1 w]
    linarith [hitTime_rec P hP hirr u v]
  set W : V → ℝ :=
    fun w => expSetHitTime P w {y} + expSetHitTime P y {z} - expSetHitTime P w {z} with hWdef
  have hWval : ∀ w : V,
      W w = expSetHitTime P w {y} + expSetHitTime P y {z} - expSetHitTime P w {z} :=
    fun w => rfl
  have hself : ∀ w : V, expSetHitTime P w {w} = 0 := by
    intro w; rw [setHit_eq P w w, if_pos rfl]
  have hWy : W y = 0 := by rw [hWval, hself y]; ring
  have hWz : 0 ≤ W z := by
    rw [hWval, hself z]
    have h1 := expSetHitTime_nonneg P hP z {y}
    have h2 := expSetHitTime_nonneg P hP y {z}
    linarith
  have hWsum : ∀ u : V, ∑ w, P u w * W w
      = (∑ w, P u w * expSetHitTime P w {y}) + expSetHitTime P y {z} * (∑ w, P u w)
        - ∑ w, P u w * expSetHitTime P w {z} := by
    intro u
    have h1 : ∀ w : V, P u w * W w
        = P u w * expSetHitTime P w {y} + expSetHitTime P y {z} * P u w
          - P u w * expSetHitTime P w {z} := by
      intro w; rw [hWval]; ring
    rw [Finset.sum_congr rfl fun w _ => h1 w, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  have hWharm : HarmonicOn P W {u : V | u ∉ ({y, z} : Finset V)} := by
    intro u hu
    simp only [Set.mem_setOf_eq] at hu
    have huy : u ≠ y := fun hcc => hu (by rw [hcc]; simp)
    have huz : u ≠ z := fun hcc => hu (by rw [hcc]; simp)
    rw [hWsum u, hP.2 u, hstepsum u y, hstepsum u z, hWval,
      setHit_eq P u y, if_neg huy, setHit_eq P u z, if_neg huz]
    ring
  set φ : V → ℝ := fun w => if w = y then 0 else W z with hφdef
  have hBne : ({y, z} : Finset V).Nonempty := ⟨y, by simp⟩
  obtain ⟨-, -, huniq⟩ := MarkovMixing.harmonic_extension P hP hirr {y, z} hBne φ
  have hWeq := huniq W (by
    intro u hu
    rcases Finset.mem_insert.mp hu with h | h
    · rw [h]
      show W y = if y = y then 0 else W z
      rw [if_pos rfl]
      exact hWy
    · rw [Finset.mem_singleton.mp h]
      show W z = if z = y then 0 else W z
      rw [if_neg (Ne.symm hyz)]) hWharm
  have hWnn : 0 ≤ W x := by
    have hx := congrFun hWeq x
    rw [hx, Finset.sum_pair hyz]
    show 0 ≤ (if y = y then 0 else W z) * firstHitAtProb P x {y, z} y
      + (if z = y then 0 else W z) * firstHitAtProb P x {y, z} z
    rw [if_pos rfl, if_neg (Ne.symm hyz), zero_mul, zero_add]
    exact mul_nonneg hWz (firstHitAt_nonneg P hP x {y, z} z)
  rw [hWval] at hWnn
  linarith

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hc : IsConductance c)
    (hpos : ∀ x : V, 0 < vertexConductance c x)
    (hirr : MarkovMixing.Irreducible (networkWalk c)) (a b z : V)
    (hab : a ≠ b) (hbz : b ≠ z) (haz : a ≠ z) :
    effectiveResistance c a z ≤
      effectiveResistance c a b + effectiveResistance c b z := by
  classical
  set P : Matrix V V ℝ := networkWalk c with hPdef
  have hPval : ∀ x y : V, P x y = c x y / vertexConductance c x := fun x y => rfl
  have hcx : ∀ x : V, vertexConductance c x ≠ 0 := fun x => ne_of_gt (hpos x)
  have hsumdiv : ∀ (u : V → ℝ) (d : ℝ), ∑ y, u y / d = (∑ y, u y) / d := by
    intro u d
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
  have hP : IsStochastic P := by
    constructor
    · intro x y; rw [hPval]; exact div_nonneg (hc.1 x y) (le_of_lt (hpos x))
    · intro x
      rw [Finset.sum_congr rfl fun y _ => hPval x y, hsumdiv]
      exact div_self (hcx x)
  have hcGpos : 0 < totalConductance c :=
    Finset.sum_pos (fun x _ => hpos x) ⟨a, Finset.mem_univ a⟩
  have ct_ab := MarkovMixing.commute_time_identity c hc hpos hirr a b hab
  have ct_bz := MarkovMixing.commute_time_identity c hc hpos hirr b z hbz
  have ct_az := MarkovMixing.commute_time_identity c hc hpos hirr a z haz
  have t1 : expSetHitTime P a {z} ≤ expSetHitTime P a {b} + expSetHitTime P b {z} :=
    hitTime_triangle P hP hirr b z hbz a
  have t2 : expSetHitTime P z {a} ≤ expSetHitTime P z {b} + expSetHitTime P b {a} :=
    hitTime_triangle P hP hirr b a (Ne.symm hab) z
  rw [← hPdef] at ct_ab ct_bz ct_az
  have hkey : totalConductance c * effectiveResistance c a z
      ≤ totalConductance c * (effectiveResistance c a b + effectiveResistance c b z) := by
    rw [← ct_az, mul_add, ← ct_ab, ← ct_bz]
    linarith
  exact le_of_mul_le_mul_left hkey hcGpos
