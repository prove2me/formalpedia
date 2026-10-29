-- Prove2me | solution 1 for HofmannMoser.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:49:14.355657+00:00
-- url     : https://prove2.me/submissions/ea1a7403-4fd9-4a99-bfa4-6594b4298ddb

import Definitions.Def_HofmannMoser_Potential
import Mathlib

universe u

namespace HMAux
open HofmannMoser

theorem foldl_mul (l : List ℕ) (a : ℕ) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [List.foldl, ih, mul_assoc]

theorem sum_filter_ite {α : Type*} (p : α → Bool) (g : α → ℕ) (l : List α) :
    ((l.filter p).map g).sum = (l.map fun x => if p x then g x else 0).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    by_cases h : p x
    · rw [List.filter_cons_of_pos h]; simp [h, ih]
    · rw [List.filter_cons_of_neg h]; simp [h, ih]

theorem sum_flatMap_map {α β γ : Type*} (la : List α) (lb : List β) (mk : α → β → γ)
    (h : γ → ℕ) :
    ((la.flatMap fun a => lb.map (mk a)).map h).sum =
      (la.map fun a => (lb.map fun b => h (mk a b)).sum).sum := by
  induction la with
  | nil => simp
  | cons a la ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons,
      List.map_map]
    rfl

variable {C : Nat → Type u}

theorem productRules_nodup (A B : TreeAutomaton C) (n : Nat) (c : C n) :
    (TreeAutomaton.productRules A B n c).Nodup := by
  classical
  set mk : ((Fin n → Fin A.stateCount) × Fin A.stateCount) →
      ((Fin n → Fin B.stateCount) × Fin B.stateCount) →
      ((Fin n → Fin (A.stateCount * B.stateCount + 1)) × Fin (A.stateCount * B.stateCount + 1)) :=
    fun ar br => (fun i ↦ productState (ar.1 i) (br.1 i), productState ar.2 br.2) with hmk
  have hinj : ∀ ar ar' br br', mk ar br = mk ar' br' → ar = ar' ∧ br = br' := by
    intro ar ar' br br' h
    simp only [hmk, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h2' := productState_injective _ _ _ _ h2
    have h1' : ∀ i, ar.1 i = ar'.1 i ∧ br.1 i = br'.1 i := fun i =>
      productState_injective _ _ _ _ (congrFun h1 i)
    exact ⟨Prod.ext (funext fun i => (h1' i).1) h2'.1, Prod.ext (funext fun i => (h1' i).2) h2'.2⟩
  have hL : ((A.rules n c).flatMap fun ar => (B.rules n c).map (mk ar)).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun ar _ => (B.no_duplicate_rules n c).map fun br br' h => (hinj _ _ _ _ h).2, ?_⟩
    refine List.Pairwise.imp ?_ (A.no_duplicate_rules n c)
    intro ar ar' hne x hx hx'
    simp only [List.mem_map] at hx hx'
    obtain ⟨br, _, rfl⟩ := hx
    obtain ⟨br', _, h⟩ := hx'
    exact hne (hinj _ _ _ _ h).1.symm
  have hpad : ((fun _ ↦ Fin.last _, Fin.last _) :
      (Fin n → Fin (A.stateCount * B.stateCount + 1)) × Fin (A.stateCount * B.stateCount + 1)) ∉
      ((A.rules n c).flatMap fun ar => (B.rules n c).map (mk ar)) := by
    intro h
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨ar, _, br, _, h⟩ := h
    have := congrArg Prod.snd h
    exact productState_ne_padding _ _ this
  unfold TreeAutomaton.productRules
  exact hL.append (List.nodup_singleton _) (fun x hx hx' => by
    simp only [List.mem_singleton] at hx'
    subst hx'
    exact hpad hx)

theorem product_runCount (S : FiniteConstructors C) (A B : TreeAutomaton C) :
    ∀ (v : Value C) (i : Fin A.stateCount) (j : Fin B.stateCount),
      (TreeAutomaton.product S A B).runCount v (productState i j) =
        A.runCount v i * B.runCount v j := by
  intro v
  induction v with
  | node c ch ih =>
    intro i j
    rename_i n
    rw [TreeAutomaton.runCount.eq_1 (TreeAutomaton.product S A B) (productState i j),
      TreeAutomaton.runCount.eq_1 A i, TreeAutomaton.runCount.eq_1 B j]
    show ((((TreeAutomaton.product S A B).rules n c).filter
        (fun tr : (Fin n → Fin (A.stateCount * B.stateCount + 1)) ×
          Fin (A.stateCount * B.stateCount + 1) => tr.2 == productState i j)).map
        fun tr => (List.ofFn fun k => (TreeAutomaton.product S A B).runCount (ch k) (tr.1 k)).foldl
          (· * ·) 1).sum = _
    have hperm : ((TreeAutomaton.product S A B).rules n c).Perm
        (TreeAutomaton.productRules A B n c) :=
      (List.perm_ext_iff_of_nodup ((TreeAutomaton.product S A B).no_duplicate_rules n c)
        (productRules_nodup A B n c)).2 (TreeAutomaton.product_rule_mem_iff S A B n c)
    have hperm' : List.Perm (α := (Fin n → Fin (A.stateCount * B.stateCount + 1)) ×
        Fin (A.stateCount * B.stateCount + 1))
        ((TreeAutomaton.product S A B).rules n c) (TreeAutomaton.productRules A B n c) := hperm
    rw [((hperm'.filter _).map _).sum_eq]
    erw [sum_filter_ite _ _ (TreeAutomaton.productRules A B n c)]
    rw [sum_filter_ite, sum_filter_ite]
    unfold TreeAutomaton.productRules
    rw [List.map_append, List.sum_append, sum_flatMap_map]
    have hpad0 : ([((fun _ ↦ Fin.last _, Fin.last _) :
        (Fin n → Fin (A.stateCount * B.stateCount + 1)) × Fin (A.stateCount * B.stateCount + 1))].map
          fun x => if (x.2 == productState i j) = true then
            (List.ofFn fun k => (TreeAutomaton.product S A B).runCount (ch k) (x.1 k)).foldl
              (· * ·) 1 else 0).sum = 0 := by
      have : ¬ (Fin.last (A.stateCount * B.stateCount) = productState i j) :=
        fun h => productState_ne_padding i j h.symm
      simp [this]
    erw [hpad0]
    rw [add_zero, ← List.sum_map_mul_right]
    congr 1
    apply List.map_congr_left
    intro ar _
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro br _
    simp only [foldl_mul, one_mul, List.prod_ofFn]
    by_cases ha : ar.2 = i
    · by_cases hb : br.2 = j
      · subst ha; subst hb
        rw [if_pos (beq_self_eq_true _), if_pos (beq_self_eq_true _), if_pos (beq_self_eq_true _),
          ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro k _
        exact ih k (ar.1 k) (br.1 k)
      · have h1 : ¬ ((productState ar.2 br.2 == productState i j) = true) := fun h =>
          hb (productState_injective _ _ _ _ (beq_iff_eq.mp h)).2
        have h3 : ¬ ((br.2 == j) = true) := fun h => hb (beq_iff_eq.mp h)
        rw [if_neg h1, if_neg h3, mul_zero]
    · have h1 : ¬ ((productState ar.2 br.2 == productState i j) = true) := fun h =>
        ha (productState_injective _ _ _ _ (beq_iff_eq.mp h)).1
      have h2 : ¬ ((ar.2 == i) = true) := fun h => ha (beq_iff_eq.mp h)
      rw [if_neg h1, if_neg h2, zero_mul]

theorem product_basic (S : FiniteConstructors C) (A B : TreeAutomaton C) (v : Value C) :
    (TreeAutomaton.product S A B).basic v = A.basic v * B.basic v :=
  product_runCount S A B v A.final B.final

theorem bf_product_val (S : FiniteConstructors C) (P : RepPolicy C) (p₁ p₂ : BasicFunction C)
    (v : Value C) : (BasicFunction.product S P p₁ p₂).val v = p₁.val v * p₂.val v := by
  show (TreeAutomaton.product S (P.rep p₁) (P.rep p₂)).basic v = _
  rw [product_basic, P.rep_basic, P.rep_basic]

end HMAux

namespace HMAux
open HofmannMoser
variable {C : Nat → Type u}

theorem mvb_eq {k : Nat} (ps : Fin k → BasicFunction C) (vals : Fin k → Value C) :
    multivariateBasic ps vals = ∏ i, (ps i).val (vals i) := by
  unfold multivariateBasic
  rw [foldl_mul, one_mul, List.prod_ofFn]

theorem sum_flatMap_mapQ {α β γ : Type*} (la : List α) (lb : List β) (mk : α → β → γ)
    (h : γ → ℚ) :
    ((la.flatMap fun a => lb.map (mk a)).map h).sum =
      (la.map fun a => (lb.map fun b => h (mk a b)).sum).sum := by
  induction la with
  | nil => simp
  | cons a la ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons,
      List.map_map]
    rfl

end HMAux

open HofmannMoser in
theorem solution {C : Nat → Type u} (S : FiniteConstructors C)
    (p : Fin 2 → BasicFunction C) :
    ∃ p' : BasicFunction C, ∀ v : Value C,
      multivariateBasic p (fun _ ↦ v) = p'.val v := by
  refine ⟨BasicFunction.product S (classicalRepPolicy C) (p 0) (p 1), fun v => ?_⟩
  rw [HMAux.bf_product_val, HMAux.mvb_eq, Fin.prod_univ_two]
