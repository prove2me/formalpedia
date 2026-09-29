-- Prove2me | solution 1 for MarkovMixing.commute_time_identity
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T16:14:54.283506+00:00
-- url     : https://prove2.me/submissions/c88658af-94af-473e-8bec-8d0586b4c47d

import Theorems.Thm_MarkovMixing_summable_hitting_tails
import Theorems.Thm_MarkovMixing_stationary_unique
import Theorems.Thm_MarkovMixing_exists_stationary_pos
import Theorems.Thm_MarkovMixing_harmonic_extension
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

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hc : IsConductance c)
    (hpos : ∀ x : V, 0 < vertexConductance c x)
    (hirr : MarkovMixing.Irreducible (networkWalk c)) (a b : V) (hab : a ≠ b) :
    expSetHitTime (networkWalk c) a {b} + expSetHitTime (networkWalk c) b {a} =
      totalConductance c * effectiveResistance c a b := by
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
  set cG : ℝ := totalConductance c with hcGdef
  have hcGpos : 0 < cG := Finset.sum_pos (fun x _ => hpos x) ⟨a, Finset.mem_univ a⟩
  set π : V → ℝ := fun x => vertexConductance c x / cG with hπdef
  have hπval : ∀ x : V, π x = vertexConductance c x / cG := fun x => rfl
  have hπpos : ∀ x : V, 0 < π x := fun x => by rw [hπval]; exact div_pos (hpos x) hcGpos
  have hπ : IsStationary P π := by
    refine ⟨⟨fun x => le_of_lt (hπpos x), ?_⟩, ?_⟩
    · rw [Finset.sum_congr rfl fun x _ => hπval x, hsumdiv]
      exact div_self (ne_of_gt hcGpos)
    · funext y
      show ∑ x, π x * P x y = π y
      have hterm : ∀ x : V, π x * P x y = c x y / cG := by
        intro x
        rw [hπval, hPval]
        field_simp
        rw [mul_comm, mul_div_assoc, div_self (hcx x), mul_one]
      rw [Finset.sum_congr rfl fun x _ => hterm x, hsumdiv, hπval]
      congr 1
      exact Finset.sum_congr rfl fun x _ => hc.2 x y
  obtain ⟨π', hst', hpos', hret'⟩ := MarkovMixing.exists_stationary_pos P hP hirr
  have hππ : π = π' := MarkovMixing.stationary_unique P hP hirr π π' hπ hst'
  have hret : ∀ x : V, π x * expHitTimePos P x x = 1 := by
    intro x; rw [hππ]; exact hret' x
  -- the one-step drift of a hitting time
  have hstepsum : ∀ x y : V,
      ∑ z, P x z * expSetHitTime P z {y} = expHitTimePos P x y - 1 := by
    intro x y
    have h1 : ∀ z : V,
        P x z * expSetHitTime P z {y} = (killed P y) x z * expHitTimePos P z y := by
      intro z
      rw [setHit_eq P z y]
      by_cases hzy : z = y
      · rw [if_pos hzy, show (killed P y) x z = 0 from by simp [killed, hzy]]; ring
      · rw [if_neg hzy, show (killed P y) x z = P x z from by simp [killed, hzy]]
    rw [Finset.sum_congr rfl fun z _ => h1 z]
    linarith [hitTime_rec P hP hirr x y]
  -- the candidate potential
  set F : V → ℝ :=
    fun x => expSetHitTime P x {b} + expSetHitTime P b {a} - expSetHitTime P x {a} with hFdef
  have hFval : ∀ x : V,
      F x = expSetHitTime P x {b} + expSetHitTime P b {a} - expSetHitTime P x {a} :=
    fun x => rfl
  have hself : ∀ x : V, expSetHitTime P x {x} = 0 := by
    intro x; rw [setHit_eq P x x, if_pos rfl]
  have hFa : F a = expSetHitTime P a {b} + expSetHitTime P b {a} := by
    rw [hFval, hself a]; ring
  have hFb : F b = 0 := by
    rw [hFval, hself b]; ring
  have hFsum : ∀ x : V, ∑ z, P x z * F z
      = (∑ z, P x z * expSetHitTime P z {b}) + expSetHitTime P b {a} * (∑ z, P x z)
        - ∑ z, P x z * expSetHitTime P z {a} := by
    intro x
    have h1 : ∀ z : V, P x z * F z
        = P x z * expSetHitTime P z {b} + expSetHitTime P b {a} * P x z
          - P x z * expSetHitTime P z {a} := by
      intro z; rw [hFval]; ring
    rw [Finset.sum_congr rfl fun z _ => h1 z, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  -- `F` is harmonic off `{a, b}`
  have hFharm : HarmonicOn P F {x : V | x ∉ ({a, b} : Finset V)} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    have hxa : x ≠ a := fun hcc => hx (by rw [hcc]; simp)
    have hxb : x ≠ b := fun hcc => hx (by rw [hcc]; simp)
    rw [hFsum x, hP.2 x, hstepsum x b, hstepsum x a, hFval,
      setHit_eq P x b, if_neg hxb, setHit_eq P x a, if_neg hxa]
    ring
  -- the drift at `a`
  have hdrift : F a - ∑ z, P a z * F z = expHitTimePos P a a := by
    rw [hFsum a, hP.2 a, hstepsum a b, hstepsum a a, hFval,
      setHit_eq P a b, if_neg hab, setHit_eq P a a, if_pos rfl]
    ring
  -- identify `F` with a multiple of the voltage
  set φ : V → ℝ := fun y => if y = a then F a else 0 with hφdef
  have hBne : ({a, b} : Finset V).Nonempty := ⟨a, by simp⟩
  obtain ⟨-, -, huniq⟩ := MarkovMixing.harmonic_extension P hP hirr {a, b} hBne φ
  have hFeq := huniq F (by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]
      show F a = if a = a then F a else 0
      rw [if_pos rfl]
    · rw [Finset.mem_singleton.mp h]
      show F b = if b = a then F a else 0
      rw [if_neg (Ne.symm hab)]
      exact hFb) hFharm
  have hFvolt : ∀ x : V, F x = F a * firstHitAtProb P x {a, b} a := by
    intro x
    have hx := congrFun hFeq x
    rw [hx, Finset.sum_pair hab]
    show (if a = a then F a else 0) * firstHitAtProb P x {a, b} a
      + (if b = a then F a else 0) * firstHitAtProb P x {a, b} b
      = F a * firstHitAtProb P x {a, b} a
    rw [if_pos rfl, if_neg (Ne.symm hab)]
    ring
  -- the voltage is the first-hit distribution at `a`
  have hvolt : ∀ x : V, voltage c a b x = firstHitAtProb P x {a, b} a := by
    intro x
    show hitBeforeProb P x a b = firstHitAtProb P x {a, b} a
    unfold firstHitAtProb hitBeforeProb
    refine (tsum_congr fun t => ?_).symm
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hiff : (ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ Fin.last t → ω i ∉ ({a, b} : Finset V)) ∧
          ω (Fin.last t) = a)
        ↔ (ω 0 = x ∧ ω (Fin.last t) = a ∧
          (∀ i : Fin (t + 1), i ≠ Fin.last t → ω i ≠ a) ∧ ∀ i : Fin (t + 1), ω i ≠ b) := by
      constructor
      · rintro ⟨h0, hav, hl⟩
        refine ⟨h0, hl, fun i hi hcc => hav i hi (by rw [hcc]; simp), fun i => ?_⟩
        by_cases hi : i = Fin.last t
        · rw [hi, hl]; exact hab
        · exact fun hcc => hav i hi (by rw [hcc]; simp)
      · rintro ⟨h0, hl, hna, hnb⟩
        refine ⟨h0, fun i hi hmem => ?_, hl⟩
        rcases Finset.mem_insert.mp hmem with h | h
        · exact hna i hi h
        · exact hnb i (Finset.mem_singleton.mp h)
    by_cases hcond : ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ Fin.last t → ω i ∉ ({a, b} : Finset V)) ∧
        ω (Fin.last t) = a
    · rw [if_pos hcond, if_pos (hiff.mp hcond)]
    · rw [if_neg hcond, if_neg (fun hd => hcond (hiff.mpr hd))]
  -- the current out of `a`
  have hcurrent : ∑ y, c a y * (F a - F y) = cG := by
    have h1 : ∀ y : V, c a y * (F a - F y)
        = vertexConductance c a * (P a y * F a - P a y * F y) := by
      intro y
      rw [hPval]
      field_simp
      rw [mul_div_assoc, div_self (hcx a), mul_one]
    rw [Finset.sum_congr rfl fun y _ => h1 y, ← Finset.mul_sum]
    have h2 : ∑ y, (P a y * F a - P a y * F y) = F a - ∑ y, P a y * F y := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hP.2 a, one_mul]
    rw [h2, hdrift]
    have h3 : π a * expHitTimePos P a a = 1 := hret a
    rw [hπval] at h3
    field_simp at h3
    linarith [h3]
  have hCcur : F a * currentStrength c a b = cG := by
    rw [← hcurrent]
    unfold currentStrength
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hvolt a, hvolt y]
    linear_combination (-(c a y)) * hFvolt a + (c a y) * hFvolt y
  have hcurne : currentStrength c a b ≠ 0 := by
    intro hcc
    rw [hcc, mul_zero] at hCcur
    exact absurd hCcur.symm (ne_of_gt hcGpos)
  show expSetHitTime P a {b} + expSetHitTime P b {a} = cG * effectiveResistance c a b
  rw [← hFa]
  unfold effectiveResistance
  field_simp
  linarith [hCcur]
