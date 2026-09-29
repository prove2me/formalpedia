-- Prove2me | solution 1 for MarkovMixing.random_target_lemma
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T15:33:32.830985+00:00
-- url     : https://prove2.me/submissions/7dddb9b3-0267-4dee-9485-d9f2090101d8

import Theorems.Thm_MarkovMixing_summable_hitting_tails
import Theorems.Thm_MarkovMixing_stationary_unique
import Theorems.Thm_MarkovMixing_exists_stationary_pos
import Theorems.Thm_MarkovMixing_harmonic_eq_const
import Definitions.Def_mm_path
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped BigOperators
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

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (a b : V) :
    ∑ y, expSetHitTime P a {y} * π y = ∑ y, expSetHitTime P b {y} * π y := by
  classical
  haveI : Nonempty V := ⟨a⟩
  -- (0) elementary bookkeeping about the two tail probabilities
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
  -- (1) the value of the tail at time `0`
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
  -- (3) summability of the tails
  have hsummable : ∀ x y : V, Summable (fun t : ℕ => avoidTailProb P x y t) :=
    fun x y => MarkovMixing.summable_hitting_tails P hP hirr x y
  -- (4) the one-step recursion for the expectations
  have hrec : ∀ x y : V,
      expHitTimePos P x y = 1 + ∑ z, (killed P y) x z * expHitTimePos P z y := by
    intro x y
    unfold expHitTimePos
    rw [(hsummable x y).tsum_eq_zero_add, hA0 x y]
    congr 1
    rw [tsum_congr fun t => hArec y t x]
    rw [Summable.tsum_finsetSum (fun z _ => (hsummable z y).mul_left _)]
    exact Finset.sum_congr rfl fun z _ => tsum_mul_left
  -- (5) the return-time identity, transported to the given `π`
  obtain ⟨π', hst', hpos', hret'⟩ := MarkovMixing.exists_stationary_pos P hP hirr
  have hππ : π = π' := MarkovMixing.stationary_unique P hP hirr π π' hπ hst'
  have hret : ∀ x : V, π x * expHitTimePos P x x = 1 := by
    intro x
    have := hret' x
    rw [hππ]
    exact this
  -- (6) a bookkeeping identity for sums with one term removed
  have hdrop : ∀ (g : V → ℝ) (x : V),
      ∑ y, (if x = y then (0 : ℝ) else g y) = (∑ y, g y) - g x := by
    intro g x
    have h1 : ∀ y : V, (if x = y then (0 : ℝ) else g y)
        = g y - (if x = y then g y else 0) := by
      intro y; split <;> ring
    rw [Finset.sum_congr rfl fun y _ => h1 y, Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp
  -- (7) the target function is harmonic
  have hharm : Harmonic P (fun x => ∑ y, expSetHitTime P x {y} * π y) := by
    intro x
    have hleft : (∑ y, expSetHitTime P x {y} * π y)
        = (∑ y, expHitTimePos P x y * π y) - 1 := by
      have hcong : ∀ y : V, expSetHitTime P x {y} * π y
          = if x = y then (0 : ℝ) else expHitTimePos P x y * π y := by
        intro y
        rw [hexpS x y]
        split <;> ring
      rw [Finset.sum_congr rfl fun y _ => hcong y,
        hdrop (fun y => expHitTimePos P x y * π y) x]
      rw [show expHitTimePos P x x * π x = 1 by rw [mul_comm]; exact hret x]
    have hright : (∑ z, P x z * ∑ y, expSetHitTime P z {y} * π y)
        = (∑ y, expHitTimePos P x y * π y) - 1 := by
      have hswap : (∑ z, P x z * ∑ y, expSetHitTime P z {y} * π y)
          = ∑ y, (∑ z, (killed P y) x z * expHitTimePos P z y) * π y := by
        rw [Finset.sum_congr rfl fun z _ => Finset.mul_sum .., Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [hexpS z y]
        by_cases hzy : z = y
        · rw [if_pos hzy, show (killed P y) x z = 0 by simp [killed, hzy]]
          ring
        · rw [if_neg hzy, show (killed P y) x z = P x z by simp [killed, hzy]]
          ring
      rw [hswap]
      have hterm : ∀ y : V, (∑ z, (killed P y) x z * expHitTimePos P z y) * π y
          = expHitTimePos P x y * π y - π y := by
        intro y
        have := hrec x y
        have hz : (∑ z, (killed P y) x z * expHitTimePos P z y)
            = expHitTimePos P x y - 1 := by linarith [this]
        rw [hz]
        ring
      rw [Finset.sum_congr rfl fun y _ => hterm y, Finset.sum_sub_distrib]
      have hπsum : ∑ y, π y = 1 := hπ.1.2
      rw [hπsum]
    show (∑ y, expSetHitTime P x {y} * π y)
        = ∑ z, P x z * ∑ y, expSetHitTime P z {y} * π y
    rw [hleft, hright]
  exact MarkovMixing.harmonic_eq_const P hP hirr _ hharm a b
