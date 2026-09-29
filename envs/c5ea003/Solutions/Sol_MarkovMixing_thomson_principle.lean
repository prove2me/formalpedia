-- Prove2me | solution 1 for MarkovMixing.thomson_principle
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T16:31:50.209925+00:00
-- url     : https://prove2.me/submissions/b212c948-649a-4c47-b642-c11b2236cde5

import Theorems.Thm_MarkovMixing_summable_hitting_tails
import Theorems.Thm_MarkovMixing_harmonic_extension
import Theorems.Thm_MarkovMixing_green_resistance
import Definitions.Def_mm_network
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open scoped BigOperators
open MarkovMixing

set_option maxRecDepth 8000

/-- The chain `Q` killed on entering the set `S`. -/
private def killedSet {W : Type*} [Fintype W] [DecidableEq W]
    (Q : Matrix W W ℝ) (S : Finset W) : Matrix W W ℝ :=
  fun a b => if b ∈ S then 0 else Q a b

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

/-- The set-avoidance path sum with a prescribed endpoint is an entry of a power of
the killed chain. -/
private lemma avoidSetAt_eq_killed_pow {W : Type*} [Fintype W] [DecidableEq W]
    (Q : Matrix W W ℝ) (S : Finset W) :
    ∀ (t : ℕ) (p₀ y : W), p₀ ∉ S →
      avoidSetAtProb Q p₀ S y t = ((killedSet Q S) ^ t) p₀ y := by
  classical
  set K := killedSet Q S with hKdef
  have hKval : ∀ a b : W, K a b = if b ∈ S then 0 else Q a b := fun a b => rfl
  intro t
  induction t with
  | zero =>
      intro p₀ y hp₀
      have hL : avoidSetAtProb Q p₀ S y 0
          = ∑ ω : Fin 1 → W, (if ω 0 = p₀ ∧ ω 0 = y then (1:ℝ) else 0) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        have hcond : (ω 0 = p₀ ∧ (∀ i : Fin 1, ω i ∉ S) ∧ ω (Fin.last 0) = y)
            ↔ (ω 0 = p₀ ∧ ω 0 = y) := by
          constructor
          · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h2⟩
            refine ⟨h1, fun i => ?_, h2⟩
            rw [Subsingleton.elim i 0, h1]
            exact hp₀
        by_cases h : ω 0 = p₀ ∧ ω 0 = y
        · rw [if_pos (hcond.mpr h), if_pos h]
          simp [pathWeight]
        · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
      rw [hL, Fintype.sum_equiv (Equiv.funUnique (Fin 1) W)
        (fun ω : Fin 1 → W => if ω 0 = p₀ ∧ ω 0 = y then (1:ℝ) else 0)
        (fun v : W => if v = p₀ ∧ v = y then (1:ℝ) else 0) (fun ω => rfl)]
      rw [pow_zero, Matrix.one_apply]
      by_cases hpy : p₀ = y
      · subst hpy
        rw [if_pos rfl, Finset.sum_eq_single p₀]
        · rw [if_pos ⟨rfl, rfl⟩]
        · intro b _ hb; rw [if_neg (fun hc => hb hc.1)]
        · intro hc; exact absurd (Finset.mem_univ p₀) hc
      · rw [if_neg hpy]
        refine Finset.sum_eq_zero fun v _ => ?_
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact hpy (h1.symm.trans h2)
  | succ n ih =>
      intro p₀ y hp₀
      have hunfold : avoidSetAtProb Q p₀ S y (n + 1)
          = ∑ ω : Fin (n + 2) → W,
              (if ω 0 = p₀ ∧ (∀ i : Fin (n + 2), ω i ∉ S) ∧
                  ω (Fin.last (n + 1)) = y then pathWeight Q ω else 0) := rfl
      rw [hunfold, ← Equiv.sum_comp (snocEquivV W n)
        (fun ω : Fin (n + 2) → W =>
          if ω 0 = p₀ ∧ (∀ i : Fin (n + 2), ω i ∉ S) ∧
              ω (Fin.last (n + 1)) = y then pathWeight Q ω else 0)]
      have hstep : ∀ p : (Fin (n + 1) → W) × W,
          (if (snocEquivV W n p) 0 = p₀ ∧
              (∀ i : Fin (n + 2), (snocEquivV W n p) i ∉ S) ∧
              (snocEquivV W n p) (Fin.last (n + 1)) = y then
            pathWeight Q (snocEquivV W n p) else 0)
          = (if (p.1 0 = p₀ ∧ ∀ i : Fin (n + 1), p.1 i ∉ S) ∧ (p.2 ∉ S ∧ p.2 = y) then
              pathWeight Q p.1 * Q (p.1 (Fin.last n)) p.2 else 0) := by
        intro p
        have hrestrict : ∀ i : Fin (n + 1), (snocEquivV W n p) i.castSucc = p.1 i :=
          fun i => snocEquivV_castSucc n p i
        have hlast : (snocEquivV W n p) (Fin.last (n + 1)) = p.2 := snocEquivV_last n p
        have hzero : (snocEquivV W n p) 0 = p.1 0 := by
          have h := hrestrict 0
          rwa [Fin.castSucc_zero] at h
        have hcond : ((snocEquivV W n p) 0 = p₀ ∧
              (∀ i : Fin (n + 2), (snocEquivV W n p) i ∉ S) ∧
              (snocEquivV W n p) (Fin.last (n + 1)) = y)
            ↔ ((p.1 0 = p₀ ∧ ∀ i : Fin (n + 1), p.1 i ∉ S) ∧ (p.2 ∉ S ∧ p.2 = y)) := by
          constructor
          · rintro ⟨h0, hne, hy⟩
            refine ⟨⟨hzero ▸ h0, fun i => ?_⟩, ?_, hlast ▸ hy⟩
            · rw [← hrestrict i]; exact hne i.castSucc
            · rw [← hlast]; exact hne _
          · rintro ⟨⟨h0, hne⟩, hlz, hy⟩
            refine ⟨hzero ▸ h0, fun i => ?_, hlast ▸ hy⟩
            induction i using Fin.lastCases with
            | last => rw [hlast]; exact hlz
            | cast j => rw [hrestrict j]; exact hne j
        have hweight : pathWeight Q (snocEquivV W n p)
            = pathWeight Q p.1 * Q (p.1 (Fin.last n)) p.2 := by
          have hpw : pathWeight Q (snocEquivV W n p)
              = ∏ i : Fin (n + 1),
                  Q ((snocEquivV W n p) i.castSucc) ((snocEquivV W n p) i.succ) := rfl
          rw [hpw, Fin.prod_univ_castSucc]
          congr 1
          · refine Finset.prod_congr rfl fun i _ => ?_
            rw [hrestrict i.castSucc]
            congr 1
            exact hrestrict i.succ
          · rw [hrestrict (Fin.last n)]
            congr 1
        by_cases h : (p.1 0 = p₀ ∧ ∀ i : Fin (n + 1), p.1 i ∉ S) ∧ (p.2 ∉ S ∧ p.2 = y)
        · rw [if_pos (hcond.mpr h), if_pos h, hweight]
        · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
      rw [Finset.sum_congr rfl fun p _ => hstep p, Fintype.sum_prod_type]
      have hinner : ∀ ω : Fin (n + 1) → W,
          (∑ v : W, if (ω 0 = p₀ ∧ ∀ i : Fin (n + 1), ω i ∉ S) ∧ (v ∉ S ∧ v = y) then
              pathWeight Q ω * Q (ω (Fin.last n)) v else 0)
          = (if ω 0 = p₀ ∧ ∀ i : Fin (n + 1), ω i ∉ S then
              pathWeight Q ω * K (ω (Fin.last n)) y else 0) := by
        intro ω
        by_cases h : ω 0 = p₀ ∧ ∀ i : Fin (n + 1), ω i ∉ S
        · rw [if_pos h]
          by_cases hyS : y ∈ S
          · rw [hKval, if_pos hyS, mul_zero]
            refine Finset.sum_eq_zero fun v _ => ?_
            rw [if_neg]
            rintro ⟨-, hvS, hvy⟩
            exact hvS (hvy ▸ hyS)
          · rw [Finset.sum_eq_single y]
            · rw [if_pos ⟨h, hyS, rfl⟩, hKval, if_neg hyS]
            · intro v _ hv
              rw [if_neg]
              rintro ⟨-, -, hvy⟩
              exact hv hvy
            · intro hc; exact absurd (Finset.mem_univ y) hc
        · rw [if_neg h]
          exact Finset.sum_eq_zero fun v _ => by rw [if_neg (fun hc => h hc.1)]
      rw [Finset.sum_congr rfl fun ω _ => hinner ω]
      rw [pow_succ]
      have hrhs : (K ^ n * K) p₀ y = ∑ w, (K ^ n) p₀ w * K w y := rfl
      rw [hrhs]
      have hexp : ∀ w : W, (K ^ n) p₀ w * K w y
          = ∑ ω : Fin (n + 1) → W,
              (if (ω 0 = p₀ ∧ (∀ i : Fin (n + 1), ω i ∉ S) ∧ ω (Fin.last n) = w) then
                pathWeight Q ω * K w y else 0) := by
        intro w
        rw [← ih p₀ w hp₀]
        have hun : avoidSetAtProb Q p₀ S w n
            = ∑ ω : Fin (n + 1) → W,
                (if (ω 0 = p₀ ∧ (∀ i : Fin (n + 1), ω i ∉ S) ∧
                    ω (Fin.last n) = w) then pathWeight Q ω else 0) := rfl
        rw [hun, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ω _ => ?_
        by_cases h : ω 0 = p₀ ∧ (∀ i : Fin (n + 1), ω i ∉ S) ∧ ω (Fin.last n) = w
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, zero_mul]
      rw [Finset.sum_congr rfl fun w _ => hexp w, Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω _ => ?_
      by_cases h : ω 0 = p₀ ∧ ∀ i : Fin (n + 1), ω i ∉ S
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

/-- The set-avoidance tail probability is the corresponding row sum. -/
private lemma setAvoidTail_eq_rowSum {W : Type*} [Fintype W] [DecidableEq W]
    (Q : Matrix W W ℝ) (S : Finset W) (t : ℕ) (p₀ : W) (hp₀ : p₀ ∉ S) :
    setAvoidTailProb Q p₀ S t = ∑ y, ((killedSet Q S) ^ t) p₀ y := by
  classical
  have hsum : ∑ y, ((killedSet Q S) ^ t) p₀ y = ∑ y, avoidSetAtProb Q p₀ S y t :=
    Finset.sum_congr rfl fun y _ => (avoidSetAt_eq_killed_pow Q S t p₀ y hp₀).symm
  rw [hsum]
  have hexp : ∀ y : W, avoidSetAtProb Q p₀ S y t
      = ∑ ω : Fin (t + 1) → W,
          (if (ω 0 = p₀ ∧ (∀ i : Fin (t + 1), ω i ∉ S) ∧ ω (Fin.last t) = y) then
            pathWeight Q ω else 0) := fun y => rfl
  rw [Finset.sum_congr rfl fun y _ => hexp y, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : ω 0 = p₀ ∧ ∀ i : Fin (t + 1), ω i ∉ S
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


/-- Summing the endpoint of the set-avoidance path sum gives the tail probability. -/
private lemma sum_avoidSetAt {W : Type*} [Fintype W] [DecidableEq W]
    (Q : Matrix W W ℝ) (S : Finset W) (t : ℕ) (p₀ : W) :
    ∑ y, avoidSetAtProb Q p₀ S y t = setAvoidTailProb Q p₀ S t := by
  classical
  have hexp : ∀ y : W, avoidSetAtProb Q p₀ S y t
      = ∑ ω : Fin (t + 1) → W,
          (if (ω 0 = p₀ ∧ (∀ i : Fin (t + 1), ω i ∉ S) ∧ ω (Fin.last t) = y) then
            pathWeight Q ω else 0) := fun y => rfl
  rw [Finset.sum_congr rfl fun y _ => hexp y, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : ω 0 = p₀ ∧ ∀ i : Fin (t + 1), ω i ∉ S
  · rw [if_pos h, Finset.sum_eq_single (ω (Fin.last t))]
    · rw [if_pos ⟨h.1, h.2, rfl⟩]
    · intro y _ hy
      rw [if_neg]
      rintro ⟨-, -, hly⟩
      exact hy hly.symm
    · intro hc; exact absurd (Finset.mem_univ _) hc
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun y _ => by
      rw [if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]

/-- First-passage probabilities at time `0`. -/
private lemma hitSetAt_zero {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (B : Finset V) (x y : V) :
    hitSetAtProb P x B y 0 = if x = y then 1 else 0 := by
  classical
  have hL : hitSetAtProb P x B y 0
      = ∑ ω : Fin 1 → V, (if ω 0 = x ∧ ω 0 = y then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hcond : (ω 0 = x ∧ (∀ i : Fin 1, i ≠ Fin.last 0 → ω i ∉ B) ∧ ω (Fin.last 0) = y)
        ↔ (ω 0 = x ∧ ω 0 = y) := by
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun i hi => absurd (Subsingleton.elim i (Fin.last 0)) hi, h2⟩
    by_cases h : ω 0 = x ∧ ω 0 = y
    · rw [if_pos (hcond.mpr h), if_pos h]
      simp [pathWeight]
    · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
  rw [hL]
  by_cases hxy : x = y
  · rw [if_pos hxy, Finset.sum_eq_single (fun _ : Fin 1 => x)]
    · rw [if_pos ⟨rfl, hxy⟩]
    · intro ω _ hne
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact hne (funext fun i => by rw [Subsingleton.elim i 0, h1])
    · intro hc; exact absurd (Finset.mem_univ _) hc
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun ω _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hxy (h1.symm.trans h2)

/-- Splitting off the last step of a first-passage trajectory. -/
private lemma hitSetAt_succ {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (B : Finset V) (x y : V) (t : ℕ) :
    hitSetAtProb P x B y (t + 1) = ∑ z, avoidSetAtProb P x B z t * P z y := by
  classical
  have hL : hitSetAtProb P x B y (t + 1)
      = ∑ ω : Fin (t + 2) → V,
          (if ω 0 = x ∧ (∀ i : Fin (t + 2), i ≠ Fin.last (t + 1) → ω i ∉ B) ∧
              ω (Fin.last (t + 1)) = y then pathWeight P ω else 0) := rfl
  rw [hL, ← Equiv.sum_comp (snocEquivV V t)
    (fun ω : Fin (t + 2) → V =>
      if ω 0 = x ∧ (∀ i : Fin (t + 2), i ≠ Fin.last (t + 1) → ω i ∉ B) ∧
          ω (Fin.last (t + 1)) = y then pathWeight P ω else 0)]
  have hstep : ∀ p : (Fin (t + 1) → V) × V,
      (if (snocEquivV V t p) 0 = x ∧
          (∀ i : Fin (t + 2), i ≠ Fin.last (t + 1) → (snocEquivV V t p) i ∉ B) ∧
          (snocEquivV V t p) (Fin.last (t + 1)) = y then
        pathWeight P (snocEquivV V t p) else 0)
      = (if (p.1 0 = x ∧ ∀ i : Fin (t + 1), p.1 i ∉ B) ∧ p.2 = y then
          pathWeight P p.1 * P (p.1 (Fin.last t)) p.2 else 0) := by
    intro p
    have hrestrict : ∀ i : Fin (t + 1), (snocEquivV V t p) i.castSucc = p.1 i :=
      fun i => snocEquivV_castSucc t p i
    have hlast : (snocEquivV V t p) (Fin.last (t + 1)) = p.2 := snocEquivV_last t p
    have hzero : (snocEquivV V t p) 0 = p.1 0 := by
      have h := hrestrict 0
      rwa [Fin.castSucc_zero] at h
    have hcond : ((snocEquivV V t p) 0 = x ∧
          (∀ i : Fin (t + 2), i ≠ Fin.last (t + 1) → (snocEquivV V t p) i ∉ B) ∧
          (snocEquivV V t p) (Fin.last (t + 1)) = y)
        ↔ ((p.1 0 = x ∧ ∀ i : Fin (t + 1), p.1 i ∉ B) ∧ p.2 = y) := by
      constructor
      · rintro ⟨h0, hne, hy⟩
        refine ⟨⟨hzero ▸ h0, fun i => ?_⟩, hlast ▸ hy⟩
        rw [← hrestrict i]
        refine hne i.castSucc ?_
        intro hc
        have h1 : (i : ℕ) = t + 1 := by
          have := congrArg Fin.val hc
          simpa using this
        have h2 := i.isLt
        omega
      · rintro ⟨⟨h0, hall⟩, hy⟩
        refine ⟨hzero ▸ h0, fun i hi => ?_, hlast ▸ hy⟩
        induction i using Fin.lastCases with
        | last => exact absurd rfl hi
        | cast j => rw [hrestrict j]; exact hall j
    have hweight : pathWeight P (snocEquivV V t p)
        = pathWeight P p.1 * P (p.1 (Fin.last t)) p.2 := by
      have hpw : pathWeight P (snocEquivV V t p)
          = ∏ i : Fin (t + 1),
              P ((snocEquivV V t p) i.castSucc) ((snocEquivV V t p) i.succ) := rfl
      rw [hpw, Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [hrestrict i.castSucc]
        congr 1
        exact hrestrict i.succ
      · rw [hrestrict (Fin.last t)]
        congr 1
    by_cases h : (p.1 0 = x ∧ ∀ i : Fin (t + 1), p.1 i ∉ B) ∧ p.2 = y
    · rw [if_pos (hcond.mpr h), if_pos h, hweight]
    · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
  rw [Finset.sum_congr rfl fun p _ => hstep p, Fintype.sum_prod_type]
  have hinner : ∀ ω : Fin (t + 1) → V,
      (∑ v : V, if (ω 0 = x ∧ ∀ i : Fin (t + 1), ω i ∉ B) ∧ v = y then
          pathWeight P ω * P (ω (Fin.last t)) v else 0)
      = (if ω 0 = x ∧ ∀ i : Fin (t + 1), ω i ∉ B then
          pathWeight P ω * P (ω (Fin.last t)) y else 0) := by
    intro ω
    by_cases h : ω 0 = x ∧ ∀ i : Fin (t + 1), ω i ∉ B
    · rw [if_pos h, Finset.sum_eq_single y]
      · rw [if_pos ⟨h, rfl⟩]
      · intro v _ hv; rw [if_neg (fun hc => hv hc.2)]
      · intro hc; exact absurd (Finset.mem_univ y) hc
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun v _ => by rw [if_neg (fun hc => h hc.1)]
  rw [Finset.sum_congr rfl fun ω _ => hinner ω]
  have hR : ∑ z, avoidSetAtProb P x B z t * P z y
      = ∑ z, ∑ ω : Fin (t + 1) → V,
          (if ω 0 = x ∧ (∀ i : Fin (t + 1), ω i ∉ B) ∧ ω (Fin.last t) = z then
            pathWeight P ω * P z y else 0) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    have hexp : avoidSetAtProb P x B z t
        = ∑ ω : Fin (t + 1) → V,
            (if ω 0 = x ∧ (∀ i : Fin (t + 1), ω i ∉ B) ∧ ω (Fin.last t) = z then
              pathWeight P ω else 0) := rfl
    rw [hexp, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h : ω 0 = x ∧ (∀ i : Fin (t + 1), ω i ∉ B) ∧ ω (Fin.last t) = z
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : ω 0 = x ∧ ∀ i : Fin (t + 1), ω i ∉ B
  · rw [if_pos h, Finset.sum_eq_single (ω (Fin.last t))]
    · rw [if_pos ⟨h.1, h.2, rfl⟩]
    · intro z _ hz
      rw [if_neg]
      rintro ⟨-, -, hlz⟩
      exact hz hlz.symm
    · intro hc; exact absurd (Finset.mem_univ _) hc
  · rw [if_neg h]
    exact (Finset.sum_eq_zero fun z _ => by
      rw [if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]).symm

/-- Trajectories avoiding `B` cannot start in `B`. -/
private lemma avoidSetAt_of_mem {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (B : Finset V) (x : V) (hx : x ∈ B) (z : V) (t : ℕ) :
    avoidSetAtProb P x B z t = 0 := by
  refine Finset.sum_eq_zero fun ω _ => ?_
  rw [if_neg]
  rintro ⟨h0, hall, -⟩
  exact hall 0 (by rw [h0]; exact hx)

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hc : IsConductance c)
    (hpos : ∀ x : V, 0 < vertexConductance c x)
    (hirr : MarkovMixing.Irreducible (networkWalk c)) (a z : V) (haz : a ≠ z) :
    effectiveResistance c a z =
      sInf {r : ℝ | ∃ θ : V → V → ℝ,
        IsFlow c θ a z ∧ flowStrength θ a = 1 ∧ r = flowEnergy c θ} ∧
    ∃ θ : V → V → ℝ, IsFlow c θ a z ∧ flowStrength θ a = 1 ∧
      effectiveResistance c a z = flowEnergy c θ := by
  classical
  haveI : Nonempty V := ⟨a⟩
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
  -- the voltage
  set W : V → ℝ := fun x => firstHitAtProb P x {a, z} a with hWdef
  set φ : V → ℝ := fun y => if y = a then (1 : ℝ) else 0 with hφdef
  obtain ⟨hb1, hb2, -⟩ :=
    MarkovMixing.harmonic_extension P hP hirr {a, z} ⟨a, by simp⟩ φ
  have hcollapse : ∀ x : V, (∑ y ∈ ({a, z} : Finset V), φ y * firstHitAtProb P x {a, z} y)
      = W x := by
    intro x
    rw [Finset.sum_pair haz]
    show (if a = a then (1 : ℝ) else 0) * firstHitAtProb P x {a, z} a
      + (if z = a then (1 : ℝ) else 0) * firstHitAtProb P x {a, z} z = W x
    rw [if_pos rfl, if_neg (Ne.symm haz), hWdef]
    ring
  have hWa : W a = 1 := by
    have := hb1 a (by simp)
    rw [hcollapse a] at this
    rw [this]
    show (if a = a then (1 : ℝ) else 0) = 1
    rw [if_pos rfl]
  have hWz : W z = 0 := by
    have := hb1 z (by simp)
    rw [hcollapse z] at this
    rw [this]
    show (if z = a then (1 : ℝ) else 0) = 0
    rw [if_neg (Ne.symm haz)]
  have hWharm : ∀ x : V, x ∉ ({a, z} : Finset V) → W x = ∑ y, P x y * W y := by
    intro x hx
    have h : (∑ y ∈ ({a, z} : Finset V), φ y * firstHitAtProb P x {a, z} y)
        = ∑ y, P x y * (∑ w ∈ ({a, z} : Finset V), φ w * firstHitAtProb P y {a, z} w) :=
      hb2 x (by simpa [Set.mem_setOf_eq] using hx)
    rw [hcollapse x] at h
    rw [h]
    exact Finset.sum_congr rfl fun y _ => by rw [hcollapse y]
  have hvolt : ∀ x : V, voltage c a z x = W x := by
    intro x
    show hitBeforeProb P x a z = W x
    rw [hWdef]
    unfold firstHitAtProb hitBeforeProb
    refine tsum_congr fun t => ?_
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hiff : (ω 0 = x ∧ ω (Fin.last t) = a ∧
          (∀ i : Fin (t + 1), i ≠ Fin.last t → ω i ≠ a) ∧ ∀ i : Fin (t + 1), ω i ≠ z)
        ↔ (ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ Fin.last t → ω i ∉ ({a, z} : Finset V)) ∧
          ω (Fin.last t) = a) := by
      constructor
      · rintro ⟨h0, hl, hna, hnz⟩
        refine ⟨h0, fun i hi hmem => ?_, hl⟩
        rcases Finset.mem_insert.mp hmem with h | h
        · exact hna i hi h
        · exact hnz i (Finset.mem_singleton.mp h)
      · rintro ⟨h0, hav, hl⟩
        refine ⟨h0, hl, fun i hi hcc => hav i hi (by rw [hcc]; simp), fun i => ?_⟩
        by_cases hi : i = Fin.last t
        · rw [hi, hl]; exact haz
        · exact fun hcc => hav i hi (by rw [hcc]; simp)
    by_cases hcond : ω 0 = x ∧ ω (Fin.last t) = a ∧
        (∀ i : Fin (t + 1), i ≠ Fin.last t → ω i ≠ a) ∧ ∀ i : Fin (t + 1), ω i ≠ z
    · rw [if_pos hcond, if_pos (hiff.mp hcond)]
    · rw [if_neg hcond, if_neg (fun hd => hcond (hiff.mpr hd))]
  -- the current strength is positive
  set I : ℝ := currentStrength c a z with hIdef
  have hIval : I = ∑ y, c a y * (W a - W y) := by
    rw [hIdef]
    unfold currentStrength
    exact Finset.sum_congr rfl fun y _ => by rw [hvolt a, hvolt y]
  have hGpos : 0 < greenFn P a z a := by
    have haz' : a ∉ ({z} : Finset V) := by simp [haz]
    have hnn : ∀ (t : ℕ) (x : V), 0 ≤ avoidSetAtProb P a {z} x t := by
      intro t x
      refine Finset.sum_nonneg fun ω _ => ?_
      split
      · exact Finset.prod_nonneg fun i _ => hP.1 _ _
      · exact le_refl 0
    have hcmp : ∀ t : ℕ, setAvoidTailProb P a {z} t ≤ avoidTailProb P a z t := by
      intro t
      refine Finset.sum_le_sum fun ω _ => ?_
      by_cases h1 : ω 0 = a ∧ ∀ i : Fin (t + 1), ω i ∉ ({z} : Finset V)
      · rw [if_pos h1, if_pos ⟨h1.1, fun i _ hi => h1.2 i (by rw [hi]; simp)⟩]
      · rw [if_neg h1]
        split
        · exact Finset.prod_nonneg fun i _ => hP.1 _ _
        · exact le_refl 0
    have hsummable : Summable (fun t : ℕ => avoidSetAtProb P a {z} a t) := by
      refine Summable.of_nonneg_of_le (fun t => hnn t a) (fun t => ?_)
        (MarkovMixing.summable_hitting_tails P hP hirr a z)
      calc avoidSetAtProb P a {z} a t ≤ ∑ y, avoidSetAtProb P a {z} y t :=
            Finset.single_le_sum (fun y _ => hnn t y) (Finset.mem_univ a)
        _ = setAvoidTailProb P a {z} t := sum_avoidSetAt P {z} t a
        _ ≤ avoidTailProb P a z t := hcmp t
    have h0 : avoidSetAtProb P a {z} a 0 = 1 := by
      rw [avoidSetAt_eq_killed_pow P {z} 0 a a haz', pow_zero, Matrix.one_apply_eq]
    have hle : avoidSetAtProb P a {z} a 0 ≤ greenFn P a z a :=
      hsummable.le_tsum 0 (fun t _ => hnn t a)
    rw [h0] at hle
    linarith
  have hRpos : 0 < effectiveResistance c a z := by
    have hg := MarkovMixing.green_resistance c hc hpos hirr a z haz
    rw [← hPdef] at hg
    nlinarith [hpos a, hGpos, hg]
  have hIpos : 0 < I := by
    have hR : effectiveResistance c a z = I⁻¹ := rfl
    rw [hR] at hRpos
    exact inv_pos.mp hRpos
  -- the Dirichlet energy identity
  have hD : ∀ x : V, x ∉ ({a, z} : Finset V) → ∑ y, c x y * (W x - W y) = 0 := by
    intro x hx
    have hterm : ∀ y : V, c x y * (W x - W y)
        = vertexConductance c x * (P x y * W x - P x y * W y) := by
      intro y
      rw [hPval]
      field_simp
      rw [mul_div_assoc, div_self (hcx x), mul_one]
    rw [Finset.sum_congr rfl fun y _ => hterm y, ← Finset.mul_sum]
    have h2 : ∑ y, (P x y * W x - P x y * W y) = W x - ∑ y, P x y * W y := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hP.2 x, one_mul]
    rw [h2, ← hWharm x hx, sub_self, mul_zero]
  have hgreen : ∑ x, ∑ y, c x y * (W x - W y) ^ 2
      = 2 * ∑ x, (W x * ∑ y, c x y * (W x - W y)) := by
    have hB : ∑ x, (W x * ∑ y, c x y * (W x - W y))
        = ∑ x, ∑ y, c x y * (W x - W y) * W x := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    have hC : ∑ x, ∑ y, c x y * (W x - W y) * W y
        = - ∑ x, ∑ y, c x y * (W x - W y) * W x := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hc.2 v u]
      ring
    have hA : ∑ x, ∑ y, c x y * (W x - W y) ^ 2
        = (∑ x, ∑ y, c x y * (W x - W y) * W x)
          - ∑ x, ∑ y, c x y * (W x - W y) * W y := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hA, hC, hB]
    ring
  have hdirichlet : ∑ x, ∑ y, c x y * (W x - W y) ^ 2 = 2 * I := by
    rw [hgreen]
    congr 1
    rw [Finset.sum_eq_single a]
    · rw [hWa, one_mul, hIval, hWa]
    · intro x _ hxa
      by_cases hxz : x = z
      · rw [hxz, hWz, zero_mul]
      · rw [hD x (by simp [hxa, hxz]), mul_zero]
    · intro hcc; exact absurd (Finset.mem_univ a) hcc
  -- the unit current flow
  set Θ : V → V → ℝ := fun x y => c x y * (W x - W y) / I with hΘdef
  have hΘval : ∀ x y : V, Θ x y = c x y * (W x - W y) / I := fun x y => rfl
  have hΘflow : IsFlow c Θ a z := by
    refine ⟨fun x y => ?_, fun x y hxy => ?_, fun x hxa hxz => ?_⟩
    · rw [hΘval, hΘval, hc.2 x y]
      field_simp
      ring
    · rw [hΘval, hxy]
      simp
    · rw [Finset.sum_congr rfl fun y _ => hΘval x y, hsumdiv,
        hD x (by simp [hxa, hxz]), zero_div]
  have hΘstr : flowStrength Θ a = 1 := by
    unfold flowStrength
    rw [Finset.sum_congr rfl fun y _ => hΘval a y, hsumdiv, ← hIval]
    exact div_self (ne_of_gt hIpos)
  have hΘenergy : flowEnergy c Θ = effectiveResistance c a z := by
    unfold flowEnergy
    have hterm : ∀ x y : V, Θ x y ^ 2 / c x y = c x y * (W x - W y) ^ 2 / I ^ 2 := by
      intro x y
      by_cases h : c x y = 0
      · rw [hΘval, h]
        simp
      · rw [hΘval]
        have hIne : I ≠ 0 := ne_of_gt hIpos
        field_simp
    rw [Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun y _ => hterm x y]
    have hsplit : ∀ x : V, ∑ y, c x y * (W x - W y) ^ 2 / I ^ 2
        = (∑ y, c x y * (W x - W y) ^ 2) / I ^ 2 := fun x => hsumdiv _ _
    rw [Finset.sum_congr rfl fun x _ => hsplit x, hsumdiv, hdirichlet]
    show 2⁻¹ * (2 * I / I ^ 2) = I⁻¹
    have hIne : I ≠ 0 := ne_of_gt hIpos
    field_simp
  -- any unit flow has at least this energy
  have hlb : ∀ θ : V → V → ℝ, IsFlow c θ a z → flowStrength θ a = 1 →
      effectiveResistance c a z ≤ flowEnergy c θ := by
    intro θ hθ hstr
    obtain ⟨hanti, hsupp, hnode⟩ := hθ
    set ψ : V → V → ℝ := fun x y => θ x y - Θ x y with hψdef
    have hψval : ∀ x y : V, ψ x y = θ x y - Θ x y := fun x y => rfl
    have hEsplit : flowEnergy c θ
        = flowEnergy c Θ + (∑ x, ∑ y, Θ x y * ψ x y / c x y) + flowEnergy c ψ := by
      unfold flowEnergy
      have hterm : ∀ x y : V, θ x y ^ 2 / c x y
          = Θ x y ^ 2 / c x y + 2 * (Θ x y * ψ x y / c x y) + ψ x y ^ 2 / c x y := by
        intro x y
        have h2 : θ x y ^ 2 = Θ x y ^ 2 + 2 * (Θ x y * ψ x y) + ψ x y ^ 2 := by
          rw [hψval]; ring
        rw [h2, add_div, add_div, mul_div_assoc]
      rw [Finset.sum_congr rfl fun x _ =>
        Finset.sum_congr rfl fun y _ => hterm x y]
      have hrow : ∀ x : V,
          (∑ y, (Θ x y ^ 2 / c x y + 2 * (Θ x y * ψ x y / c x y) + ψ x y ^ 2 / c x y))
            = (∑ y, Θ x y ^ 2 / c x y) + 2 * (∑ y, Θ x y * ψ x y / c x y)
              + ∑ y, ψ x y ^ 2 / c x y := by
        intro x
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_congr rfl fun x _ => hrow x, Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    have hψanti : ∀ x y : V, ψ x y = -ψ y x := by
      intro x y
      rw [hψval, hψval, hanti x y, hΘval, hΘval, hc.2 x y]
      field_simp
      ring
    have hstr' : ∑ y, θ a y = 1 := hstr
    have hΘstr' : ∑ y, Θ a y = 1 := hΘstr
    have hcross : ∑ x, ∑ y, Θ x y * ψ x y / c x y = 0 := by
      have hterm : ∀ x y : V, Θ x y * ψ x y / c x y = (W x - W y) * ψ x y / I := by
        intro x y
        by_cases h : c x y = 0
        · rw [hΘval, h, hψval, hΘval, h, hsupp x y h]
          simp
        · rw [hΘval]
          field_simp
      rw [Finset.sum_congr rfl fun x _ =>
        Finset.sum_congr rfl fun y _ => hterm x y]
      have hSzero : ∀ x : V, W x * (∑ y, ψ x y) = 0 := by
        intro x
        have hSx : ∑ y, ψ x y = (∑ y, θ x y) - ∑ y, Θ x y := by
          rw [← Finset.sum_sub_distrib]
        by_cases hxz : x = z
        · rw [hxz, hWz, zero_mul]
        · by_cases hxa : x = a
          · rw [hSx, hxa, hstr', hΘstr', sub_self, mul_zero]
          · rw [hSx, hnode x hxa hxz, hΘflow.2.2 x hxa hxz, sub_self, mul_zero]
      have hA : ∑ x, ∑ y, W x * ψ x y = 0 := by
        have h1 : ∀ x : V, ∑ y, W x * ψ x y = W x * ∑ y, ψ x y := by
          intro x; rw [Finset.mul_sum]
        rw [Finset.sum_congr rfl fun x _ => h1 x]
        exact Finset.sum_eq_zero fun x _ => hSzero x
      have hB : ∑ x, ∑ y, W y * ψ x y = 0 := by
        rw [Finset.sum_comm]
        have h1 : ∀ y : V, ∑ x, W y * ψ x y = -(W y * ∑ x, ψ y x) := by
          intro y
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hψanti x y]
          ring
        rw [Finset.sum_congr rfl fun y _ => h1 y]
        exact Finset.sum_eq_zero fun y _ => by rw [hSzero y]; ring
      have hAB : ∑ x, ∑ y, (W x - W y) * ψ x y = 0 := by
        have hsub : ∀ x : V, ∑ y, (W x - W y) * ψ x y
            = (∑ y, W x * ψ x y) - ∑ y, W y * ψ x y := by
          intro x
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun y _ => by ring
        rw [Finset.sum_congr rfl fun x _ => hsub x, Finset.sum_sub_distrib, hA, hB, sub_zero]
      rw [Finset.sum_congr rfl fun x _ => hsumdiv (fun y => (W x - W y) * ψ x y) I, hsumdiv,
        hAB, zero_div]
    have hψnn : 0 ≤ flowEnergy c ψ := by
      unfold flowEnergy
      have hnn : (0 : ℝ) ≤ ∑ x, ∑ y, ψ x y ^ 2 / c x y :=
        Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
          div_nonneg (sq_nonneg _) (hc.1 x y)
      linarith
    rw [← hΘenergy]
    linarith
  refine ⟨?_, Θ, hΘflow, hΘstr, hΘenergy.symm⟩
  have hmem : effectiveResistance c a z ∈ {r : ℝ | ∃ θ : V → V → ℝ,
      IsFlow c θ a z ∧ flowStrength θ a = 1 ∧ r = flowEnergy c θ} :=
    ⟨Θ, hΘflow, hΘstr, hΘenergy.symm⟩
  have hlow : ∀ r ∈ {r : ℝ | ∃ θ : V → V → ℝ,
      IsFlow c θ a z ∧ flowStrength θ a = 1 ∧ r = flowEnergy c θ},
      effectiveResistance c a z ≤ r := by
    rintro r ⟨θ, hθ, hstr, rfl⟩
    exact hlb θ hθ hstr
  exact le_antisymm (le_csInf ⟨_, hmem⟩ hlow)
    (csInf_le ⟨effectiveResistance c a z, fun r hr => hlow r hr⟩ hmem)
