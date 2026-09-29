-- Prove2me | solution 1 for AlmostLossless.exists_quadratic_rate_scanScheme
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T14:19:38.124823+00:00
-- url     : https://prove2.me/submissions/e56d475d-2b8c-4028-b64d-6800455607e2

import Definitions.Def_Logic_AlmostLossless_Core
import Definitions.Def_Logic_AlmostLossless_Instances
import Definitions.Def_Logic_AlmostLossless_Scheme
open AlmostLossless in
theorem solution {S : Type*} [Fintype S] [DecidableEq S] (T : Finset S) (hT : T.Nonempty) :
    ∃ p : ℕ, p.Prime ∧ T.card ^ 2 < p ∧ p ≤ 2 * T.card ^ 2 ∧
      ∃ (a : Fin (Fintype.card S) → ZMod p)
        (P : ScanScheme S (Fin (Fintype.card S) → ZMod p) (ZMod p)),
        P.typical = T ∧ Honest (P.code a) ∧ (∀ s ∈ T, Correct (P.code a) s) ∧
        (∀ m : ZMod p, P.decodeCost a m = T.card) := by
  have hcard : T.card ≠ 0 := (Finset.card_pos.mpr hT).ne'
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (T.card ^ 2) (pow_ne_zero 2 hcard)
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hlt, hle, ?_⟩
  have hTp : T.card < p := lt_of_le_of_lt (Nat.le_self_pow two_ne_zero _) hlt
  let hsh : (Fin (Fintype.card S) → ZMod p) → S → ZMod p :=
    fun _ s => if h : s ∈ T then ((T.equivFin ⟨s, h⟩ : ℕ) : ZMod p) else 0
  let P : ScanScheme S (Fin (Fintype.card S) → ZMod p) (ZMod p) := linearScan T hsh
  have hinj : ∀ a, ∀ x ∈ P.typical, ∀ y ∈ P.typical, P.hash a x = P.hash a y → x = y := by
    intro a x hx y hy hxy
    have hx' : x ∈ T := hx
    have hy' : y ∈ T := hy
    have hxy' : ((T.equivFin ⟨x, hx'⟩ : ℕ) : ZMod p) = ((T.equivFin ⟨y, hy'⟩ : ℕ) : ZMod p) := by
      have : hsh a x = hsh a y := hxy
      simpa only [hsh, dif_pos hx', dif_pos hy'] using this
    have hxl := (T.equivFin ⟨x, hx'⟩).isLt
    have hyl := (T.equivFin ⟨y, hy'⟩).isLt
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ p).mp hxy'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    have := T.equivFin.injective (Fin.ext hmod)
    exact congrArg Subtype.val this
  have hscan0 : ∀ (p : S → Bool) (L : List S) (st : ScanState S),
      L.filter p = [] → L.foldl (scanStep p) st = st := by
    intro p L
    induction L with
    | nil => intro st _; rfl
    | cons a t ih =>
      intro st h
      rw [List.filter_cons] at h
      by_cases ha : p a = true
      · rw [if_pos ha] at h
        simp at h
      · rw [if_neg ha] at h
        simp only [List.foldl_cons, scanStep, ha, Bool.false_eq_true, if_false]
        exact ih st h
  have hscan1 : ∀ (p : S → Bool) (L : List S) (x : S),
      L.filter p = [x] → L.foldl (scanStep p) .empty = .unique x := by
    intro p L x
    induction L with
    | nil => intro h; simp at h
    | cons a t ih =>
      intro h
      rw [List.filter_cons] at h
      split_ifs at h with ha
      · simp only [List.cons.injEq] at h
        obtain ⟨rfl, ht⟩ := h
        simp only [List.foldl_cons, scanStep, ha, if_true]
        exact hscan0 p t _ ht
      · simp only [List.foldl_cons, scanStep, ha, Bool.false_eq_true, if_false]
        exact ih h
  have hfs : ∀ (q : S → Prop) [DecidablePred q] (x : S) (L : List S), L.Nodup → x ∈ L →
      (∀ y ∈ L, q y → y = x) → q x → L.filter (fun z => decide (q z)) = [x] := by
    intro q _ x L
    induction L with
    | nil => intro _ hx; simp at hx
    | cons a t ih =>
      intro hnd hx huniq hqx
      rw [List.nodup_cons] at hnd
      by_cases hax : a = x
      · subst hax
        have hnil : t.filter (fun z => decide (q z)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro y hy hyq
          have := huniq y (List.mem_cons_of_mem _ hy) (by simpa using hyq)
          exact hnd.1 (this ▸ hy)
        simp [hnil, hqx]
      · have hxt : x ∈ t := by
          rcases List.mem_cons.mp hx with h1 | h1
          · exact absurd h1.symm hax
          · exact h1
        have hqa : ¬ q a := fun hq => hax (huniq a List.mem_cons_self hq)
        rw [List.filter_cons, if_neg (by simpa using hqa)]
        exact ih hnd.2 hxt (fun y hy hyq => huniq y (List.mem_cons_of_mem _ hy) hyq) hqx
  have hcorrect : ∀ a : Fin (Fintype.card S) → ZMod p, (∀ x ∈ P.typical, ∀ y ∈ P.typical, P.hash a x = P.hash a y → x = y) →
      ∀ s ∈ P.typical, Correct (P.code a) s := by
    intro a hinj s hs
    show (P.code a).dec ((P.code a).enc s) = some s
    have henc : (P.code a).enc s = some (P.hash a s) := by
      simp only [ScanScheme.code, if_pos hs]
    rw [henc]
    show P.decode a (P.hash a s) = some s
    have hfilt : ((P.cand a (P.hash a s)).toList).filter
        (fun t => decide (P.hash a t = P.hash a s)) = [s] := by
      apply hfs (fun t => P.hash a t = P.hash a s) s _ (Finset.nodup_toList _)
      · rw [Finset.mem_toList]; exact P.self_mem_cand a s hs
      · intro y hy hyh
        rw [Finset.mem_toList] at hy
        exact hinj y (P.cand_subset a _ hy) s hs hyh
      · rfl
    unfold ScanScheme.decode scan
    rw [hscan1 _ _ s hfilt]
  refine ⟨0, P, rfl, ?_, fun s hs => hcorrect 0 (hinj 0) s hs, fun m => rfl⟩
  intro s
  by_cases hs : s ∈ T
  · exact Or.inl (hcorrect 0 (hinj 0) s hs)
  · right
    have henc : (P.code 0).enc s = none := by
      simp only [ScanScheme.code, P, linearScan, if_neg hs]
    show (P.code 0).dec ((P.code 0).enc s) = none
    rw [henc]
    rfl
