-- Prove2me | solution 1 for MarkovMixing.harmonic_extension
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T15:56:02.283731+00:00
-- url     : https://prove2.me/submissions/a126587d-8a69-4630-ac68-7e33d2654299

import Theorems.Thm_MarkovMixing_summable_hitting_tails
import Definitions.Def_mm_network
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.InfiniteSum.Real

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
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (B : Finset V) (hB : B.Nonempty) (f : V → ℝ) :
    (∀ x ∈ B, (∑ y ∈ B, f y * firstHitAtProb P x B y) = f x) ∧
    HarmonicOn P (fun x => ∑ y ∈ B, f y * firstHitAtProb P x B y)
      {x : V | x ∉ B} ∧
    ∀ g : V → ℝ, (∀ x ∈ B, g x = f x) → HarmonicOn P g {x : V | x ∉ B} →
      g = fun x => ∑ y ∈ B, f y * firstHitAtProb P x B y := by
  classical
  obtain ⟨b₀, hb₀⟩ := hB
  haveI : Nonempty V := ⟨b₀⟩
  -- basic positivity facts
  have hpwnn : ∀ (t : ℕ) (ω : Fin (t + 1) → V), 0 ≤ pathWeight P ω :=
    fun t ω => Finset.prod_nonneg fun i _ => hP.1 _ _
  have havnn : ∀ (x z : V) (t : ℕ), 0 ≤ avoidSetAtProb P x B z t := by
    intro x z t
    refine Finset.sum_nonneg fun ω _ => ?_
    split
    · exact hpwnn t ω
    · exact le_refl 0
  have hhitnn : ∀ (x y : V) (t : ℕ), 0 ≤ hitSetAtProb P x B y t := by
    intro x y t
    refine Finset.sum_nonneg fun ω _ => ?_
    split
    · exact hpwnn t ω
    · exact le_refl 0
  have hPle1 : ∀ z y : V, P z y ≤ 1 := by
    intro z y
    have := Finset.single_le_sum (f := fun w => P z w) (fun w _ => hP.1 z w)
      (Finset.mem_univ y)
    rwa [hP.2 z] at this
  have hpownn : ∀ (n : ℕ) (x y : V), 0 ≤ (P ^ n) x y := by
    intro n
    induction n with
    | zero => intro x y; by_cases hxy : x = y <;> simp [Matrix.one_apply, hxy]
    | succ m ih =>
        intro x y
        have : (P ^ (m + 1)) x y = ∑ z, (P ^ m) x z * P z y := by rw [pow_succ]; rfl
        rw [this]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)
  -- comparison with the single-state avoidance probabilities
  have hcmp : ∀ (w : V) (t : ℕ), setAvoidTailProb P w B t ≤ avoidTailProb P w b₀ t := by
    intro w t
    refine Finset.sum_le_sum fun ω _ => ?_
    by_cases h1 : ω 0 = w ∧ ∀ i : Fin (t + 1), ω i ∉ B
    · rw [if_pos h1, if_pos ⟨h1.1, fun i _ hi => h1.2 i (by rw [hi]; exact hb₀)⟩]
    · rw [if_neg h1]
      split
      · exact hpwnn t ω
      · exact le_refl 0
  have hbound : ∀ (w : V), w ∉ B → ∀ (y : V) (t : ℕ),
      hitSetAtProb P w B y (t + 1) ≤ avoidTailProb P w b₀ t := by
    intro w hw y t
    rw [hitSetAt_succ]
    calc ∑ z, avoidSetAtProb P w B z t * P z y
        ≤ ∑ z, avoidSetAtProb P w B z t := by
          refine Finset.sum_le_sum fun z _ => ?_
          calc avoidSetAtProb P w B z t * P z y
              ≤ avoidSetAtProb P w B z t * 1 :=
                mul_le_mul_of_nonneg_left (hPle1 z y) (havnn w z t)
            _ = avoidSetAtProb P w B z t := mul_one _
      _ = setAvoidTailProb P w B t := sum_avoidSetAt P B t w
      _ ≤ avoidTailProb P w b₀ t := hcmp w t
  have hsummable : ∀ w y : V, Summable (fun t : ℕ => hitSetAtProb P w B y t) := by
    intro w y
    rw [← summable_nat_add_iff 1]
    by_cases hw : w ∈ B
    · have hz : (fun t : ℕ => hitSetAtProb P w B y (t + 1)) = fun _ => (0 : ℝ) := by
        funext t
        rw [hitSetAt_succ]
        exact Finset.sum_eq_zero fun z _ => by
          rw [avoidSetAt_of_mem P B w hw z t, zero_mul]
      rw [hz]
      exact summable_zero
    · exact Summable.of_nonneg_of_le (fun t => hhitnn w y (t + 1))
        (fun t => hbound w hw y t) (MarkovMixing.summable_hitting_tails P hP hirr w b₀)
  -- first-passage probabilities started inside `B`
  have hfirst_mem : ∀ x ∈ B, ∀ y : V,
      firstHitAtProb P x B y = if x = y then 1 else 0 := by
    intro x hx y
    have hzero : ∀ t : ℕ, t ≠ 0 → hitSetAtProb P x B y t = 0 := by
      intro t ht
      obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
      rw [hitSetAt_succ]
      exact Finset.sum_eq_zero fun z _ => by
        rw [avoidSetAt_of_mem P B x hx z t', zero_mul]
    unfold firstHitAtProb
    rw [tsum_eq_single 0 hzero]
    exact hitSetAt_zero P B x y
  -- the first-step recursion off `B`
  have hstep : ∀ x : V, x ∉ B → ∀ (z : V) (t : ℕ),
      avoidSetAtProb P x B z (t + 1) = ∑ w, P x w * avoidSetAtProb P w B z t := by
    intro x hx z t
    rw [avoidSetAt_eq_killed_pow P B (t + 1) x z hx]
    have hp : ((killedSet P B) ^ (t + 1)) x z
        = ∑ w, (killedSet P B) x w * ((killedSet P B) ^ t) w z := by
      rw [pow_succ']; rfl
    rw [hp]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : w ∈ B
    · rw [show (killedSet P B) x w = 0 from by simp [killedSet, hw],
        avoidSetAt_of_mem P B w hw z t, zero_mul, mul_zero]
    · rw [show (killedSet P B) x w = P x w from by simp [killedSet, hw],
        avoidSetAt_eq_killed_pow P B t w z hw]
  have hrec : ∀ x : V, x ∉ B → ∀ (y : V) (t : ℕ),
      hitSetAtProb P x B y (t + 1) = ∑ w, P x w * hitSetAtProb P w B y t := by
    intro x hx y t
    cases t with
    | zero =>
        rw [hitSetAt_succ]
        have h0 : ∀ z : V, avoidSetAtProb P x B z 0 = if x = z then (1 : ℝ) else 0 := by
          intro z
          rw [avoidSetAt_eq_killed_pow P B 0 x z hx, pow_zero, Matrix.one_apply]
        have hL : ∑ z, avoidSetAtProb P x B z 0 * P z y = P x y := by
          rw [Finset.sum_congr rfl fun z _ => by rw [h0 z], Finset.sum_eq_single x]
          · rw [if_pos rfl, one_mul]
          · intro z _ hz
            rw [if_neg (Ne.symm hz), zero_mul]
          · intro hc; exact absurd (Finset.mem_univ x) hc
        have hR : ∑ w, P x w * hitSetAtProb P w B y 0 = P x y := by
          rw [Finset.sum_congr rfl fun w _ => by rw [hitSetAt_zero P B w y],
            Finset.sum_eq_single y]
          · rw [if_pos rfl, mul_one]
          · intro w _ hw
            rw [if_neg hw, mul_zero]
          · intro hc; exact absurd (Finset.mem_univ y) hc
        rw [hL, hR]
    | succ t' =>
        rw [hitSetAt_succ]
        rw [Finset.sum_congr rfl fun z _ => by rw [hstep x hx z t', Finset.sum_mul]]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hitSetAt_succ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
  have hharm_first : ∀ x : V, x ∉ B → ∀ y ∈ B,
      firstHitAtProb P x B y = ∑ w, P x w * firstHitAtProb P w B y := by
    intro x hx y hy
    unfold firstHitAtProb
    rw [(hsummable x y).tsum_eq_zero_add, hitSetAt_zero P B x y,
      if_neg (fun hc => hx (by rw [hc]; exact hy))]
    rw [tsum_congr fun t => hrec x hx y t]
    rw [Summable.tsum_finsetSum (fun w _ => (hsummable w y).mul_left _), zero_add]
    exact Finset.sum_congr rfl fun w _ => tsum_mul_left
  -- part 1: the boundary values
  have part1 : ∀ x ∈ B, (∑ y ∈ B, f y * firstHitAtProb P x B y) = f x := by
    intro x hx
    rw [Finset.sum_congr rfl fun y _ => by rw [hfirst_mem x hx y], Finset.sum_eq_single x]
    · rw [if_pos rfl, mul_one]
    · intro y _ hy
      rw [if_neg (Ne.symm hy), mul_zero]
    · intro hc; exact absurd hx hc
  -- part 2: harmonicity off `B`
  have part2 : HarmonicOn P (fun x => ∑ y ∈ B, f y * firstHitAtProb P x B y)
      {x : V | x ∉ B} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    show (∑ y ∈ B, f y * firstHitAtProb P x B y)
      = ∑ w, P x w * ∑ y ∈ B, f y * firstHitAtProb P w B y
    rw [Finset.sum_congr rfl fun y hy => by
      rw [hharm_first x hx y hy, Finset.mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  refine ⟨part1, part2, ?_⟩
  -- part 3: uniqueness, via the maximum principle
  have key : ∀ v : V → ℝ, (∀ x ∈ B, v x = 0) →
      (∀ x : V, x ∉ B → v x = ∑ w, P x w * v w) → ∀ x : V, v x ≤ 0 := by
    intro v hv0 hvH
    obtain ⟨x₀, -, hx₀⟩ :=
      Finset.exists_max_image (Finset.univ : Finset V) v ⟨b₀, Finset.mem_univ b₀⟩
    by_cases hmem : ∃ b ∈ B, v b = v x₀
    · obtain ⟨b, hbB, hb⟩ := hmem
      intro x
      have hle : v x ≤ v x₀ := hx₀ x (Finset.mem_univ x)
      rw [← hb, hv0 b hbB] at hle
      exact hle
    · exfalso
      push Not at hmem
      have hAnB : ∀ x : V, v x = v x₀ → x ∉ B := fun x hx hxB => hmem x hxB hx
      have hclosed : ∀ x : V, v x = v x₀ → ∀ z : V, 0 < P x z → v z = v x₀ := by
        intro x hx z hz
        have hxB : x ∉ B := hAnB x hx
        have heq : v x = ∑ w, P x w * v w := hvH x hxB
        have hsum0 : ∑ w, P x w * (v x₀ - v w) = 0 := by
          have hexp : ∑ w, P x w * (v x₀ - v w)
              = (∑ w, P x w) * v x₀ - ∑ w, P x w * v w := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun w _ => by ring
          rw [hexp, hP.2 x, one_mul, ← heq, hx]
          ring
        have hterms : ∀ w ∈ (Finset.univ : Finset V), 0 ≤ P x w * (v x₀ - v w) := by
          intro w _
          refine mul_nonneg (hP.1 x w) ?_
          have := hx₀ w (Finset.mem_univ w)
          linarith
        have hz0 := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsum0 z (Finset.mem_univ z)
        rcases mul_eq_zero.mp hz0 with hc | hc
        · exact absurd hc (ne_of_gt hz)
        · linarith [hc]
      have hreach : ∀ (t : ℕ) (z : V), 0 < (P ^ t) x₀ z → v z = v x₀ := by
        intro t
        induction t with
        | zero =>
            intro z hz
            rw [pow_zero] at hz
            by_cases hzx : x₀ = z
            · rw [← hzx]
            · rw [Matrix.one_apply_ne hzx] at hz
              exact absurd hz (lt_irrefl 0)
        | succ n ih =>
            intro z hz
            have hexp : (P ^ (n + 1)) x₀ z = ∑ w, (P ^ n) x₀ w * P w z := by
              rw [pow_succ]; rfl
            rw [hexp] at hz
            obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hz)
            obtain ⟨hw1, hw2⟩ := mul_ne_zero_iff.mp hw
            exact hclosed w (ih w (lt_of_le_of_ne (hpownn n x₀ w) (Ne.symm hw1))) z
              (lt_of_le_of_ne (hP.1 w z) (Ne.symm hw2))
      obtain ⟨t, ht⟩ := hirr x₀ b₀
      exact hAnB b₀ (hreach t b₀ ht) hb₀
  intro g hgB hgH
  funext x
  have huB : ∀ x ∈ B, g x - (∑ y ∈ B, f y * firstHitAtProb P x B y) = 0 := by
    intro x hx
    rw [hgB x hx, part1 x hx]
    ring
  have huH : ∀ x : V, x ∉ B →
      g x - (∑ y ∈ B, f y * firstHitAtProb P x B y)
        = ∑ w, P x w * (g w - ∑ y ∈ B, f y * firstHitAtProb P w B y) := by
    intro x hx
    have h1 : g x = ∑ w, P x w * g w := hgH x (by simp [Set.mem_setOf_eq, hx])
    have h2 : (∑ y ∈ B, f y * firstHitAtProb P x B y)
        = ∑ w, P x w * ∑ y ∈ B, f y * firstHitAtProb P w B y :=
      part2 x (by simp [Set.mem_setOf_eq, hx])
    rw [h1, h2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  have hle1 := key (fun x => g x - ∑ y ∈ B, f y * firstHitAtProb P x B y) huB huH x
  have hle2 := key (fun x => -(g x - ∑ y ∈ B, f y * firstHitAtProb P x B y))
    (fun z hz => by simp [huB z hz])
    (fun z hz => by
      show -(g z - ∑ y ∈ B, f y * firstHitAtProb P z B y)
        = ∑ w, P z w * -(g w - ∑ y ∈ B, f y * firstHitAtProb P w B y)
      rw [huH z hz, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring) x
  simp only at hle1 hle2
  show g x = ∑ y ∈ B, f y * firstHitAtProb P x B y
  linarith
