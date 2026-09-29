-- Prove2me | solution 2 for AlmostLossless.avgFailProb_scanCode_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T13:08:01.904183+00:00
-- url     : https://prove2.me/submissions/c80d7fe8-3058-4615-940d-ff86bd0d3935

import Definitions.Def_Logic_AlmostLossless_Core
import Definitions.Def_Logic_AlmostLossless_Hashing
import Definitions.Def_Logic_AlmostLossless_Scheme
open AlmostLossless in
theorem solution {S A M : Type*} [DecidableEq S] [DecidableEq M] [Fintype S] [Fintype A]
    [DecidableEq A] [Nonempty A] [Fintype M] [Nonempty M]
    (μ : Source S) (P : ScanScheme S A M)
    (hu : TwoUniversal P.hash) (ε : ℚ) (hε : 0 ≤ ε) (hT : 1 - ε ≤ μ.prob P.typical) :
    avgFailProb μ (fun a => P.code a)
      ≤ ε + (P.typical.offDiag.card : ℚ) / (Fintype.card M : ℚ) := by
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
  have hcorrect : ∀ a : A, (∀ x ∈ P.typical, ∀ y ∈ P.typical, P.hash a x = P.hash a y → x = y) →
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
  have hfail_le1 : ∀ a, failProb μ (P.code a) ≤ 1 := by
    intro a
    unfold failProb
    calc ∑ s ∈ ({s | ¬ Correct (P.code a) s} : Finset S), μ.w s ≤ ∑ s, μ.w s :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun s _ _ => μ.nonneg s)
      _ = 1 := μ.total
  have htot : ∑ s ∈ P.typicalᶜ, μ.w s + μ.prob P.typical = 1 := by
    unfold Source.prob
    rw [Finset.sum_compl_add_sum]
    exact μ.total
  have hseed : ∀ a, failProb μ (P.code a)
      ≤ ε + (if CollidesOn P.hash P.typical a then (1 : ℚ) else 0) := by
    intro a
    split_ifs with hc
    · linarith [hfail_le1 a]
    · have hinj : ∀ x ∈ P.typical, ∀ y ∈ P.typical, P.hash a x = P.hash a y → x = y := by
        intro x hx y hy hxy
        by_contra hne
        exact hc ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hne⟩, hxy⟩
      have hsub : ({s | ¬ Correct (P.code a) s} : Finset S) ⊆ P.typicalᶜ := by
        intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
        rw [Finset.mem_compl]
        exact fun hsT => hs (hcorrect a hinj s hsT)
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ => μ.nonneg s) (f := μ.w)
      unfold failProb
      linarith
  have hcoll : ((Finset.univ.filter (fun a => CollidesOn P.hash P.typical a)).card : ℚ)
      * (Fintype.card M : ℚ) ≤ (P.typical.offDiag.card : ℚ) * (Fintype.card A : ℚ) := by
    have hsub : Finset.univ.filter (fun a => CollidesOn P.hash P.typical a)
        ⊆ P.typical.offDiag.biUnion
            (fun p => Finset.univ.filter (fun a => P.hash a p.1 = P.hash a p.2)) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, CollidesOn] at ha
      obtain ⟨p, hp, hpa⟩ := ha
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p, hp, hpa⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := P.typical.offDiag)
      (t := fun p => Finset.univ.filter (fun a => P.hash a p.1 = P.hash a p.2))
    have h4 : (∑ p ∈ P.typical.offDiag,
        (Finset.univ.filter (fun a => P.hash a p.1 = P.hash a p.2)).card) * Fintype.card M
          ≤ P.typical.offDiag.card * Fintype.card A := by
      rw [Finset.sum_mul]
      calc ∑ p ∈ P.typical.offDiag,
            (Finset.univ.filter (fun a => P.hash a p.1 = P.hash a p.2)).card * Fintype.card M
          ≤ ∑ _p ∈ P.typical.offDiag, Fintype.card A :=
            Finset.sum_le_sum (fun p hp => hu p.1 p.2 (Finset.mem_offDiag.mp hp).2.2)
        _ = P.typical.offDiag.card * Fintype.card A := by simp
    have h5 : (Finset.univ.filter (fun a => CollidesOn P.hash P.typical a)).card * Fintype.card M
        ≤ P.typical.offDiag.card * Fintype.card A :=
      le_trans (Nat.mul_le_mul_right _ (h1.trans h2)) h4
    exact_mod_cast h5
  unfold avgFailProb
  have hA : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hM : (0 : ℚ) < Fintype.card M := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hA]
  have hcoll' : ((Finset.univ.filter (fun a => CollidesOn P.hash P.typical a)).card : ℚ)
      ≤ (P.typical.offDiag.card : ℚ) / (Fintype.card M : ℚ) * (Fintype.card A : ℚ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hM]
    linarith
  calc ∑ a, failProb μ (P.code a)
      ≤ ∑ a, (ε + (if CollidesOn P.hash P.typical a then (1 : ℚ) else 0)) :=
        Finset.sum_le_sum (fun a _ => hseed a)
    _ = ε * (Fintype.card A : ℚ)
        + ((Finset.univ.filter (fun a => CollidesOn P.hash P.typical a)).card : ℚ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Finset.sum_boole, mul_comm]
    _ ≤ (ε + (P.typical.offDiag.card : ℚ) / (Fintype.card M : ℚ)) * (Fintype.card A : ℚ) := by
        rw [add_mul]
        linarith
