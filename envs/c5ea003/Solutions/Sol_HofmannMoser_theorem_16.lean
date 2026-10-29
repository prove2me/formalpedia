-- Prove2me | solution 1 for HofmannMoser.theorem_16
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-29T04:38:49.37264+00:00
-- url     : https://prove2.me/submissions/c400681e-2518-411d-8fdc-813eed675de7

import Definitions.Def_HofmannMoser_Typing
import Theorems.Thm_HofmannMoser_lemma_12
import Theorems.Thm_HofmannMoser_lemma_13
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith

/-!
Potential and tensor-contraction infrastructure for Hofmann--Moser (TLCA 2015).

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
-/

set_option autoImplicit false

noncomputable section
open scoped ENNReal
open HofmannMoser
namespace HMProof
universe u v
variable {C : Nat → Type u}
attribute [local instance] Classical.propDecidable

def lift (q : Rat) : ℝ≥0∞ := ENNReal.ofReal (q : ℝ)

@[simp] theorem lift_zero : lift 0 = 0 := by simp [lift]
@[simp] theorem lift_one : lift 1 = 1 := by simp [lift]
theorem lift_add {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    lift (a + b) = lift a + lift b := by
  simp only [lift, Rat.cast_add]
  exact ENNReal.ofReal_add (by exact_mod_cast ha) (by exact_mod_cast hb)
theorem lift_mul {a b : Rat} (ha : 0 ≤ a) : lift (a*b) = lift a * lift b := by
  simp only [lift, Rat.cast_mul]
  exact ENNReal.ofReal_mul (by exact_mod_cast ha)
theorem lift_mono {a b : Rat} (h : a ≤ b) : lift a ≤ lift b := by
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast h)
theorem lift_le_iff {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    lift a ≤ lift b ↔ a ≤ b := by
  rw [lift, lift, ENNReal.ofReal_le_ofReal_iff (by exact_mod_cast hb)]
  exact Rat.cast_le

@[simp] theorem lift_nat (n : Nat) : lift (n : Rat) = (n : ℝ≥0∞) := by
  simp [lift]

theorem potential_nonneg {n : Nat} (Q : Annotation C n) (vs : Fin n → Value C) :
    0 ≤ potential Q vs := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg e.2.2 (Nat.cast_nonneg _)

theorem coefficient_nonneg {n : Nat} (Q : Annotation C n) (ps : Fin n → BasicFunction C) :
    0 ≤ annotationCoefficient Q ps := by
  classical
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  split <;> first | exact e.2.2 | exact le_rfl

theorem coefficientList_nonneg {n : Nat} (Q : Annotation C n) (ps : List (BasicFunction C)) :
    0 ≤ annotationCoefficientList Q ps := by
  classical
  unfold annotationCoefficientList
  split <;> first | exact coefficient_nonneg _ _ | exact le_rfl

/-- Summation over lists with prescribed length. -/
def lsum {α : Type u} (n : Nat) (f : List α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x : {x : List α // x.length = n}, f x.1

theorem lsum_congr {α : Type u} {n : Nat} {f g : List α → ℝ≥0∞}
    (h : ∀ x, x.length = n → f x = g x) : lsum n f = lsum n g := by
  apply tsum_congr
  intro x
  exact h x.1 x.2

theorem lsum_mono {α : Type u} {n : Nat} {f g : List α → ℝ≥0∞}
    (h : ∀ x, x.length = n → f x ≤ g x) : lsum n f ≤ lsum n g := by
  exact ENNReal.tsum_le_tsum (fun x => h x.1 x.2)

@[simp] theorem lsum_zero {α : Type u} (n : Nat) : lsum (α := α) n (fun _ => 0) = 0 := by
  simp [lsum]

theorem lsum_add {α : Type u} (n : Nat) (f g : List α → ℝ≥0∞) :
    lsum n (fun x => f x + g x) = lsum n f + lsum n g := by
  exact ENNReal.tsum_add

theorem lsum_mul_left {α : Type u} (n : Nat) (c : ℝ≥0∞) (f : List α → ℝ≥0∞) :
    lsum n (fun x => c * f x) = c * lsum n f := by
  exact ENNReal.tsum_mul_left

theorem lsum_mul_right {α : Type u} (n : Nat) (f : List α → ℝ≥0∞) (c : ℝ≥0∞) :
    lsum n (fun x => f x * c) = lsum n f * c := by
  exact ENNReal.tsum_mul_right

theorem lsum_comm {α : Type u} {β : Type v} (n m : Nat) (f : List α → List β → ℝ≥0∞) :
    lsum n (fun x => lsum m (f x)) = lsum m (fun y => lsum n (fun x => f x y)) := by
  exact ENNReal.tsum_comm

def appendEquiv {α : Type u} (n m : Nat) :
    ({x : List α // x.length = n} × {x : List α // x.length = m}) ≃
      {x : List α // x.length = n+m} where
  toFun x := ⟨x.1.1 ++ x.2.1, by simp [x.1.2, x.2.2]⟩
  invFun x := (⟨x.1.take n, by simp [x.2]⟩,
    ⟨x.1.drop n, by simp [x.2]⟩)
  left_inv x := by
    apply Prod.ext <;> apply Subtype.ext
    · exact List.take_left' x.1.2
    · exact List.drop_left' x.1.2
  right_inv x := by apply Subtype.ext; exact List.take_append_drop _ _

theorem lsum_append {α : Type u} (n m : Nat) (f : List α → ℝ≥0∞) :
    lsum (n+m) f = lsum n (fun a => lsum m (fun b => f (a++b))) := by
  unfold lsum
  change _ = ∑' (a : {x : List α // x.length = n}) (b : {x : List α // x.length = m}), f (a.1 ++ b.1)
  calc
    _ = ∑' p : {x : List α // x.length = n} × {x : List α // x.length = m},
        f (p.1.1 ++ p.2.1) := (Equiv.tsum_eq (appendEquiv n m) (fun x => f x.1)).symm
    _ = _ := ENNReal.tsum_prod' 

@[simp] theorem lsum_nil {α : Type u} (f : List α → ℝ≥0∞) : lsum 0 f = f [] := by
  unfold lsum
  have h : ∀ x : {x : List α // x.length = 0}, x = ⟨[], rfl⟩ := by
    intro x; apply Subtype.ext; exact List.length_eq_zero_iff.mp x.2
  rw [tsum_eq_single ⟨[], rfl⟩ (by intro x hx; exact (hx (h x)).elim)]

@[simp] theorem lsum_singleton {α : Type u} (f : List α → ℝ≥0∞) :
    lsum 1 f = ∑' a : α, f [a] := by
  let e : α ≃ {x : List α // x.length = 1} := {
    toFun := fun a => ⟨[a], rfl⟩
    invFun := fun x => x.1[0]'(by omega)
    left_inv := by intro a; rfl
    right_inv := by
      intro x; apply Subtype.ext
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp x.2
      simp [ha] }
  exact (Equiv.tsum_eq e (fun x => f x.1)).symm

/-- Product of basic functions evaluated against a list of values. -/
def weight (ps : List (BasicFunction C)) (vs : List (Value C)) : ℝ≥0∞ :=
  (List.zipWith (fun p v => (p.val v : ℝ≥0∞)) ps vs).prod

@[simp] theorem weight_nil_left (vs : List (Value C)) : weight [] vs = 1 := by
  simp [weight]
@[simp] theorem weight_nil_right (ps : List (BasicFunction C)) : weight ps [] = 1 := by
  simp [weight]
@[simp] theorem weight_singleton (p : BasicFunction C) (v : Value C) :
    weight [p] [v] = (p.val v : ℝ≥0∞) := by simp [weight]

theorem weight_append (a b : List (BasicFunction C)) (vs ws : List (Value C))
    (h : a.length = vs.length) : weight (a++b) (vs++ws) = weight a vs * weight b ws := by
  unfold weight
  rw [List.zipWith_append h, List.prod_append]

@[simp] theorem coefficientList_cons {n : Nat}
    (e : (Fin n → BasicFunction C) × {q : Rat // 0 ≤ q})
    (Q : Annotation C n) (ps : List (BasicFunction C)) :
    annotationCoefficientList (e::Q) ps =
      (if List.ofFn e.1 = ps then e.2.1 else 0) + annotationCoefficientList Q ps := by
  classical
  unfold annotationCoefficientList
  by_cases h : ps.length = n
  · simp only [dif_pos h, annotationCoefficient, List.map_cons, List.sum_cons]
    have hget : List.ofFn (fun i : Fin n => ps.get ⟨i.val, by omega⟩) = ps := by
      subst n
      exact List.ofFn_get ps
    have hkey : e.1 = (fun i : Fin n => ps.get ⟨i.val, by omega⟩) ↔ List.ofFn e.1 = ps := by
      constructor
      · intro heq
        rw [heq]
        exact hget
      · intro heq
        apply List.ofFn_injective
        exact heq.trans hget.symm
    rw [hkey]
    split_ifs <;> rfl
  · simp only [dif_neg h, add_zero]
    rw [if_neg]
    intro heq
    apply h
    rw [← heq, List.length_ofFn]

@[simp] theorem coefficientList_nil {n : Nat} (ps : List (BasicFunction C)) :
    annotationCoefficientList ([] : Annotation C n) ps = 0 := by
  classical
  unfold annotationCoefficientList annotationCoefficient
  split <;> simp

theorem weight_ofFn {n : Nat} (ps : Fin n → BasicFunction C) (vs : Fin n → Value C) :
    weight (List.ofFn ps) (List.ofFn vs) = (multivariateBasic ps vs : ℝ≥0∞) := by
  have hfold : ∀ (l : List Nat) (a : Nat), l.foldl (· * ·) a = a * l.prod := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons x l ih => intro a; simp [List.foldl, ih, mul_assoc]
  have hz : List.zipWith (fun p v => (p.val v : ℝ≥0∞)) (List.ofFn ps) (List.ofFn vs) =
      List.ofFn (fun i => ((ps i).val (vs i) : ℝ≥0∞)) := by
    apply List.ext_getElem <;> simp
  rw [weight, hz]
  simp only [multivariateBasic, hfold, one_mul]
  simp
  rfl

/-- Finitely supported annotation evaluation expressed as a nonnegative tensor sum. -/
theorem lsum_potential {n : Nat} (Q : Annotation C n) (vs : Fin n → Value C) :
    lsum n (fun ps => lift (annotationCoefficientList Q ps) * weight ps (List.ofFn vs)) =
      lift (potential Q vs) := by
  classical
  induction Q with
  | nil => simp [potential]
  | cons e Q ih =>
    simp only [coefficientList_cons]
    have he : ∀ ps : List (BasicFunction C), 0 ≤ (if List.ofFn e.1 = ps then e.2.1 else 0) :=
      fun ps => by split <;> first | exact e.2.2 | exact le_rfl
    simp_rw [lift_add (he _) (coefficientList_nonneg _ _), add_mul]
    rw [lsum_add, ih]
    have hsingle : lsum n (fun ps =>
        lift (if List.ofFn e.1 = ps then e.2.1 else 0) * weight ps (List.ofFn vs)) =
        lift e.2.1 * weight (List.ofFn e.1) (List.ofFn vs) := by
      unfold lsum
      rw [tsum_eq_single (⟨List.ofFn e.1, List.length_ofFn⟩ :
        {ps : List (BasicFunction C) // ps.length = n})]
      · simp
      · intro x hx
        have hne : List.ofFn e.1 ≠ x.1 := by
          intro heq; apply hx; apply Subtype.ext; exact heq.symm
        simp [hne]
    rw [hsingle, weight_ofFn]
    change _ = lift (e.2.1 * (multivariateBasic e.1 vs : Rat) + potential Q vs)
    rw [lift_add (mul_nonneg e.2.2 (Nat.cast_nonneg _)) (potential_nonneg _ _),
      lift_mul e.2.2, lift_nat]

theorem canonical_val (S : FiniteConstructors C) (v : Value C) :
    (BasicFunction.canonical S).val v = 1 := by
  have hfold : ∀ (l : List Nat) (a : Nat), l.foldl (· * ·) a = a * l.prod := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons x l ih => intro a; simp [List.foldl, ih, mul_assoc]
  have hc : ∀ (v : Value C) (q : Fin 1), (TreeAutomaton.canonical S).runCount v q = 1 := by
    intro v
    induction v with
    | node c ch ih =>
      intro q
      have hq : q = 0 := Subsingleton.elim _ _
      subst q
      rw [TreeAutomaton.runCount.eq_1]
      simp only [TreeAutomaton.canonical] at ih
      simp [TreeAutomaton.canonical, hfold, ih]
  exact hc v 0

@[simp] theorem weight_canonical (S : FiniteConstructors C) (n : Nat) (vs : List (Value C)) :
    weight (List.replicate n (BasicFunction.canonical S)) vs = 1 := by
  induction vs generalizing n with
  | nil => simp
  | cons v vs ih =>
    cases n with
    | zero => simp
    | succ n => simpa [weight, List.replicate_succ, canonical_val] using ih n

def charge (mode : TypingMode) (m : Nat) : ℝ≥0∞ :=
  if mode = .counted then (m : ℝ≥0∞) else 0

@[simp] theorem charge_counted (m : Nat) : charge .counted m = m := by simp [charge]
@[simp] theorem charge_costFree (m : Nat) : charge .costFree m = 0 := by simp [charge]

theorem charge_le_lsum (S : FiniteConstructors C) (mode : TypingMode)
    (n cost : Nat) (vs : List (Value C)) :
    charge mode cost ≤ lsum n (fun ps =>
      charge (listPremiseMode S mode ps) cost * weight ps vs) := by
  cases mode with
  | costFree => simp only [charge_costFree]; exact bot_le
  | counted =>
    have hmode : listPremiseMode S .counted (List.replicate n (BasicFunction.canonical S)) =
        .counted := by simp [listPremiseMode]
    have hpoint := ENNReal.le_tsum (f := fun ps : {ps : List (BasicFunction C) // ps.length = n} =>
      charge (listPremiseMode S .counted ps.1) cost * weight ps.1 vs)
      ⟨List.replicate n (BasicFunction.canonical S), List.length_replicate⟩
    simpa [lsum, hmode] using hpoint

/-- Weighted argument bounds compose. Only the canonical index pays the counted
cost; its weight is one. All other weights are nonnegative. -/
theorem weighted_argument (S : FiniteConstructors C) (mode : TypingMode)
    {n : Nat} (others cost : Nat) (vs : Fin n → Value C) (v : Value C)
    (ws : List (Value C))
    (P : List (BasicFunction C) → Annotation C n)
    (R : List (BasicFunction C) → Annotation C 1)
    (h : ∀ ps, ps.length = others →
      lift (potential (R ps) (fun _ => v)) + charge (listPremiseMode S mode ps) cost ≤
        lift (potential (P ps) vs)) :
    lsum others (fun ps => lift (potential (R ps) (fun _ => v)) * weight ps ws) +
      charge mode cost ≤
    lsum others (fun ps => lift (potential (P ps) vs) * weight ps ws) := by
  calc
    _ ≤ lsum others (fun ps => lift (potential (R ps) (fun _ => v)) * weight ps ws) +
        lsum others (fun ps => charge (listPremiseMode S mode ps) cost * weight ps ws) :=
      add_le_add le_rfl (charge_le_lsum S mode others cost ws)
    _ = lsum others (fun ps =>
        (lift (potential (R ps) (fun _ => v)) + charge (listPremiseMode S mode ps) cost) *
          weight ps ws) := by simp_rw [add_mul]; rw [lsum_add]
    _ ≤ _ := lsum_mono (fun ps hp => mul_le_mul_right' (h ps hp) _)

theorem potential_mono {n : Nat} {P Q : Annotation C n} (h : annotationLe P Q)
    (vs : Fin n → Value C) : potential P vs ≤ potential Q vs := by
  apply (lift_le_iff (potential_nonneg _ _) (potential_nonneg _ _)).mp
  rw [← lsum_potential P vs, ← lsum_potential Q vs]
  apply lsum_mono
  intro ps hp
  apply mul_le_mul_right'
  apply lift_mono
  unfold annotationCoefficientList
  simp only [dif_pos hp]
  exact h _

theorem potential_eq {n : Nat} {P Q : Annotation C n} (h : annotationEq P Q)
    (vs : Fin n → Value C) : potential P vs = potential Q vs := by
  exact le_antisymm (potential_mono (fun i => (h i).le) vs)
    (potential_mono (fun i => (h i).ge) vs)

/-- Expand a weighted family of potentials into its three independent indices. -/
theorem contract_expand {n : Nat} (a b : Nat)
    (P : List (BasicFunction C) → Annotation C n) (vs : Fin n → Value C)
    (before after : List (Value C)) (hb : before.length = a) :
    lsum (a+b) (fun j => lift (potential (P j) vs) * weight j (before++after)) =
    lsum a (fun bs => lsum b (fun ds => lsum n (fun cs =>
      lift (annotationCoefficientList (P (bs++ds)) cs) * weight cs (List.ofFn vs) *
        weight bs before * weight ds after))) := by
  rw [lsum_append]
  apply lsum_congr
  intro bs hbs
  apply lsum_congr
  intro ds hds
  rw [← lsum_potential]
  rw [← lsum_mul_right]
  apply lsum_congr
  intro cs hcs
  rw [weight_append bs ds before after (hbs.trans hb.symm)]
  ac_rfl

/-- The coefficient equation between two consecutive composition premises is
exactly a tensor transposition after evaluating the surrounding arguments. -/
theorem tensor_transpose (a n b : Nat)
    (P : List (BasicFunction C) → Annotation C n)
    (R : List (BasicFunction C) → Annotation C 1)
    (before after : List (Value C)) (hb : before.length = a)
    (vs : Fin n → Value C) (v : Value C)
    (hc : ∀ bs cs ds os, bs.length = a → cs.length = n → ds.length = b →
      os.length = 1 →
      annotationCoefficientList (P (bs++os++ds)) cs =
        annotationCoefficientList (R (bs++cs++ds)) os) :
    lsum (a+n+b) (fun j => lift (potential (R j) (fun _ => v)) *
      weight j (before++List.ofFn vs++after)) =
    lsum (a+1+b) (fun j => lift (potential (P j) vs) *
      weight j (before++[v]++after)) := by
  have hassoc : a+n+b = a+(n+b) := by omega
  have hassoc' : a+1+b = a+(1+b) := by omega
  rw [hassoc, hassoc']
  simp only [List.append_assoc]
  rw [contract_expand a (n+b) R (fun _ => v) before (List.ofFn vs++after) hb,
      contract_expand a (1+b) P vs before ([v]++after) hb]
  apply lsum_congr
  intro bs hbs
  rw [lsum_append n b, lsum_append 1 b]
  have hleft :
      lsum n (fun cs => lsum b (fun ds => lsum 1 (fun os =>
        lift (annotationCoefficientList (R (bs++(cs++ds))) os) *
          weight os (List.ofFn (fun _ : Fin 1 => v)) * weight bs before *
            weight (cs++ds) (List.ofFn vs++after)))) =
      lsum 1 (fun os => lsum b (fun ds => lsum n (fun cs =>
        lift (annotationCoefficientList (R (bs++(cs++ds))) os) *
          weight os (List.ofFn (fun _ : Fin 1 => v)) * weight bs before *
            weight (cs++ds) (List.ofFn vs++after)))) := by
    simp_rw [lsum_comm b 1]
    rw [lsum_comm n 1]
    apply lsum_congr
    intro os hos
    rw [lsum_comm n b]
  rw [hleft]
  apply lsum_congr
  intro os hos
  apply lsum_congr
  intro ds hds
  apply lsum_congr
  intro cs hcs
  have hcoef := hc bs cs ds os hbs hcs hds hos
  simp only [List.append_assoc] at hcoef
  rw [← hcoef]
  rw [weight_append cs ds (List.ofFn vs) after (by simpa using hcs),
      weight_append os ds [v] after (by simpa using hos)]
  simp only [List.ofFn_const, List.replicate_one]
  ac_rfl

theorem contract_join {n m : Nat} (Q : Annotation C (n+m))
    (P : List (BasicFunction C) → Annotation C n)
    (vs : Fin n → Value C) (ws : List (Value C))
    (all : Fin (n+m) → Value C) (hv : List.ofFn all = List.ofFn vs ++ ws)
    (hc : ∀ cs ds, cs.length = n → ds.length = m →
      annotationCoefficientList Q (cs++ds) = annotationCoefficientList (P ds) cs) :
    lsum m (fun ds => lift (potential (P ds) vs) * weight ds ws) = lift (potential Q all) := by
  rw [← lsum_potential Q all, hv, lsum_append, lsum_comm]
  apply lsum_congr
  intro ds hds
  rw [← lsum_potential (P ds) vs, ← lsum_mul_right]
  apply lsum_congr
  intro cs hcs
  rw [hc cs ds hcs hds, weight_append cs ds (List.ofFn vs) ws (by simpa using hcs)]
  ac_rfl

theorem contract_join_right {n m : Nat} (Q : Annotation C (n+m))
    (R : List (BasicFunction C) → Annotation C m)
    (vs : List (Value C)) (ws : Fin m → Value C) (hlen : vs.length = n)
    (all : Fin (n+m) → Value C) (hv : List.ofFn all = vs ++ List.ofFn ws)
    (hc : ∀ cs ds, cs.length = n → ds.length = m →
      annotationCoefficientList Q (cs++ds) = annotationCoefficientList (R cs) ds) :
    lsum n (fun cs => lift (potential (R cs) ws) * weight cs vs) = lift (potential Q all) := by
  rw [← lsum_potential Q all, hv, lsum_append]
  apply lsum_congr
  intro cs hcs
  rw [← lsum_potential (R cs) ws, ← lsum_mul_right]
  apply lsum_congr
  intro ds hds
  rw [hc cs ds hcs hds, weight_append cs ds vs (List.ofFn ws) (hcs.trans hlen.symm)]
  ac_rfl

/-- Concatenate a consecutive interval of argument value blocks. -/
def valueBlocks (values : Nat → List (Value C)) (start stop : Nat) : List (Value C) :=
  (List.range (stop-start)).flatMap (fun k => values (start+k))

@[simp] theorem valueBlocks_length (values : Nat → List (Value C)) (start stop : Nat) :
    (valueBlocks values start stop).length =
      contextWidth (fun i => (values i).length) start stop := by
  simp [valueBlocks, contextWidth, List.length_flatMap]

@[simp] theorem valueBlocks_empty (values : Nat → List (Value C)) (start stop : Nat)
    (h : stop ≤ start) : valueBlocks values start stop = [] := by
  simp [valueBlocks, Nat.sub_eq_zero_of_le h]

theorem valueBlocks_head (values : Nat → List (Value C)) (start stop : Nat) (h : start < stop) :
    valueBlocks values start stop = values start ++ valueBlocks values (start+1) stop := by
  have hsub : stop-start = (stop-(start+1))+1 := by omega
  unfold valueBlocks
  rw [hsub, List.range_succ_eq_map]
  simp only [List.flatMap_cons, List.flatMap_map, Nat.add_zero]
  congr 1
  congr 1
  funext k
  congr 1
  omega

theorem contextWidth_head (lengths : Nat → Nat) (start stop : Nat) (h : start < stop) :
    contextWidth lengths start stop = lengths start + contextWidth lengths (start+1) stop := by
  have hsub : stop-start = (stop-(start+1))+1 := by omega
  unfold contextWidth
  rw [hsub, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, List.sum_cons, Nat.add_zero]
  apply congrArg (fun z => lengths start + z)
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  dsimp
  congr 1
  omega

@[simp] theorem potential_cast {n m : Nat} (h : n=m) (Q : Annotation C n)
    (vs : Fin m → Value C) :
    potential (h ▸ Q) vs = potential Q (fun i => vs (Fin.cast h i)) := by
  subst m
  rfl

@[simp] theorem coefficientList_cast {n m : Nat} (h : n=m) (Q : Annotation C n)
    (ps : List (BasicFunction C)) :
    annotationCoefficientList (h ▸ Q) ps = annotationCoefficientList Q ps := by
  subst m
  rfl

@[simp] theorem ofFn_cast {α : Type u} {n m : Nat} (h : n=m) (f : Fin m → α) :
    List.ofFn (fun i => f (Fin.cast h i)) = List.ofFn f := by
  subst m
  rfl

theorem ofFn_nat {α : Type u} (f : Nat → α) (n : Nat) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  apply List.ext_getElem <;> simp

/-- The full n-ary potential contraction in Figure 2. This lemma concerns only
nonnegative annotations and the displayed coefficient equations; the evaluation
and typing inductions supply its argument inequalities. -/
theorem composition_potential (S : FiniteConstructors C) (mode : TypingMode)
    (last : Nat) (lengths : Nat → Nat)
    (Q : Annotation C (contextWidth lengths 0 (last+1)))
    (S' : Annotation C (last+1))
    (P : (i : Nat) → List (BasicFunction C) → Annotation C (lengths i))
    (R : Nat → List (BasicFunction C) → Annotation C 1)
    (hcoef : compositionCoefficients last lengths Q S' P R)
    (values : (i : Nat) → Fin (lengths i) → Value C)
    (outputs : Nat → Value C) (costs : Nat → Nat)
    (all : Fin (contextWidth lengths 0 (last+1)) → Value C)
    (hall : List.ofFn all = valueBlocks (fun i => List.ofFn (values i)) 0 (last+1))
    (hargs : ∀ i, i < last+1 → ∀ ps,
      ps.length = i + contextWidth lengths (i+1) (last+1) →
      lift (potential (R i ps) (fun _ => outputs i)) +
        charge (listPremiseMode S mode ps) (costs i) ≤
      lift (potential (P i ps) (values i))) :
    lift (potential S' (fun i => outputs i.val)) +
      charge mode (((List.range (last+1)).map costs).sum) ≤ lift (potential Q all) := by
  let tail := fun i => contextWidth lengths (i+1) (last+1)
  let blocks := fun a => valueBlocks (fun i => List.ofFn (values i)) a (last+1)
  let outPrefix := fun a => (List.range a).map outputs
  let L := fun i => lsum (i+tail i) (fun ps =>
    lift (potential (P i ps) (values i)) * weight ps (outPrefix i ++ blocks (i+1)))
  let U := fun i => lsum (i+tail i) (fun ps =>
    lift (potential (R i ps) (fun _ => outputs i)) * weight ps (outPrefix i ++ blocks (i+1)))
  have hstep : ∀ i, i < last+1 → U i + charge mode (costs i) ≤ L i := by
    intro i hi
    exact weighted_argument S mode (i+tail i) (costs i) (values i) (outputs i)
      (outPrefix i ++ blocks (i+1)) (P i) (R i) (hargs i hi)
  have hadj : ∀ i, i < last → U i = L (i+1) := by
    intro i hi
    have hw : tail i = lengths (i+1) + tail (i+1) :=
      contextWidth_head lengths (i+1) (last+1) (by omega)
    have hb : blocks (i+1) = List.ofFn (values (i+1)) ++ blocks (i+2) :=
      valueBlocks_head _ (i+1) (last+1) (by omega)
    have hp : outPrefix (i+1) = outPrefix i ++ [outputs i] := by
      simp [outPrefix, List.range_succ]
    have ht := tensor_transpose i (lengths (i+1)) (tail (i+1)) (P (i+1)) (R i)
      (outPrefix i) (blocks (i+2)) (by simp [outPrefix]) (values (i+1)) (outputs i) ?_
    · simpa only [U, L, hw, hb, hp, Nat.add_assoc, List.append_assoc, Nat.reduceAdd] using ht
    · intro bs cs ds os hbs hcs hds hos
      obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp hos
      exact hcoef.2.1 i hi bs cs ds output hbs hcs hds
  have hfirst : L 0 = lift (potential Q all) := by
    have hw : contextWidth lengths 0 (last+1) = lengths 0 + tail 0 :=
      contextWidth_head lengths 0 (last+1) (by omega)
    let Q0 : Annotation C (lengths 0 + tail 0) := hw ▸ Q
    let all0 : Fin (lengths 0 + tail 0) → Value C := fun i => all (Fin.cast hw.symm i)
    have hv : List.ofFn all0 = List.ofFn (values 0) ++ blocks 1 := by
      rw [ofFn_cast, hall]
      exact valueBlocks_head _ 0 (last+1) (by omega)
    have hcall := contract_join Q0 (P 0) (values 0) (blocks 1) all0 hv ?_
    · simpa [L, outPrefix, Q0, all0] using hcall
    · intro cs ds hcs hds
      simpa [Q0] using hcoef.1 cs ds hcs hds
  have hlast : U last = lift (potential S' (fun i => outputs i.val)) := by
    have ht : tail last = 0 := by simp [tail, contextWidth]
    have hb : blocks (last+1) = [] := valueBlocks_empty _ _ _ le_rfl
    have hv : List.ofFn (fun i : Fin (last+1) => outputs i.val) =
        outPrefix last ++ List.ofFn (fun _ : Fin 1 => outputs last) := by
      rw [ofFn_nat outputs (last+1), List.range_succ, List.map_append]
      simp [outPrefix]
    have hcall := contract_join_right S' (R last) (outPrefix last)
      (fun _ : Fin 1 => outputs last) (by simp [outPrefix])
      (fun i => outputs i.val) hv ?_
    · simpa [U, ht, hb] using hcall
    · intro cs ds hcs hds
      obtain ⟨output, rfl⟩ := List.length_eq_one_iff.mp hds
      exact hcoef.2.2 cs output hcs
  have hcharge : ∀ i, charge mode (((List.range (i+2)).map costs).sum) =
      charge mode (((List.range (i+1)).map costs).sum) + charge mode (costs (i+1)) := by
    intro i
    cases mode <;> simp [charge, List.range_succ, add_assoc]
  have hchain : ∀ i, i ≤ last →
      U i + charge mode (((List.range (i+1)).map costs).sum) ≤ L 0 := by
    intro i
    induction i with
    | zero => intro hi; simpa using hstep 0 (by omega)
    | succ i ih =>
      intro hi
      have hi' := ih (by omega)
      have hs := hstep (i+1) (by omega)
      rw [← hadj i (by omega)] at hs
      rw [show i+1+1 = i+2 by omega, hcharge]
      calc
        _ = (U (i+1) + charge mode (costs (i+1))) +
            charge mode (((List.range (i+1)).map costs).sum) := by ac_rfl
        _ ≤ U i + charge mode (((List.range (i+1)).map costs).sum) := add_le_add hs le_rfl
        _ ≤ L 0 := hi'
  simpa only [hlast, hfirst] using hchain last le_rfl

end HMProof

noncomputable section
universe u
open HofmannMoser
namespace HMProof
variable {C D : Nat → Type u}

namespace Term

theorem subst_congr_on (t : HofmannMoser.Term C D) (a b : Nat → HofmannMoser.Term C D)
    (h : ∀ x ∈ t.variables, a x = b x) : t.subst a = t.subst b := by
  induction t with
  | var x => exact h x (by simp [HofmannMoser.Term.variables])
  | func f args ih =>
    change HofmannMoser.Term.func f (fun i => (args i).subst a) = HofmannMoser.Term.func f (fun i => (args i).subst b)
    congr 1
    funext i
    apply ih i
    intro x hx
    apply h
    simp only [HofmannMoser.Term.variables, List.mem_flatMap, List.mem_finRange, true_and]
    exact ⟨i, hx⟩

theorem subst_subst (t : HofmannMoser.Term C D)
    (a b : Nat → HofmannMoser.Term C D) :
    (t.subst a).subst b = t.subst (fun x => (a x).subst b) := by
  induction t with
  | var x => rfl
  | func f args ih =>
    change HofmannMoser.Term.func f (fun i => ((args i).subst a).subst b) =
      HofmannMoser.Term.func f (fun i => (args i).subst (fun x => (a x).subst b))
    congr 1
    funext i
    exact ih i

theorem variables_rename (t : HofmannMoser.Term C D) (ρ : Nat → Nat) :
    (t.rename ρ).variables = t.variables.map ρ := by
  induction t with
  | var x => rfl
  | func f args ih =>
    simp only [HofmannMoser.Term.rename, HofmannMoser.Term.subst,
      HofmannMoser.Term.variables, List.map_flatMap]
    congr 1
    funext i
    exact ih i

end Term

@[simp] theorem value_subst (v : Value C) (a : Nat → HofmannMoser.Term C D) :
    v.toTerm.subst a = v.toTerm := by
  induction v with
  | node c ch ih =>
    change HofmannMoser.Term.func (.inl c) (fun i => (ch i).toTerm.subst a) =
      HofmannMoser.Term.func (.inl c) (fun i => (ch i).toTerm)
    congr 1
    funext i
    exact ih i

set_option maxHeartbeats 50000

/-- A closed evaluation, bounded by a derivation fuel. Constructor values can be
read at any fuel. Recursive computation premises consume one unit of fuel;
only defined-function rewrites consume counted cost. -/
inductive GroundEval (R : RewriteSystem C D) : Nat → Term C D → Nat → Value C → Prop
  | value (fuel : Nat) (v : Value C) : GroundEval R fuel v.toTerm 0 v
  | constructor (fuel : Nat) {n : Nat} (c : C n) (ts : Fin n → Term C D)
      (costs : Fin n → Nat) (vs : Fin n → Value C)
      (hargs : ∀ i, GroundEval R fuel (ts i) (costs i) (vs i)) :
      GroundEval R (fuel+1) (.func (.inl c) ts)
        (((List.finRange n).map costs).sum) (.node c vs)
  | rewrite (fuel : Nat) {n : Nat} (f : D n) (ts : Fin n → Term C D)
      (costs : Fin n → Nat) (vs : Fin n → Value C)
      (hargs : ∀ i, GroundEval R fuel (ts i) (costs i) (vs i))
      (r : Rule C D) (hr : R r) (ha : r.arity = n) (hf : ha ▸ r.symbol = f)
      (β : Nat → Value C)
      (hmatch : ∀ i, (vs i).toTerm =
        (r.patterns (Fin.cast ha.symm i)).subst (fun x => (β x).toTerm))
      (m : Nat) (v : Value C)
      (hbody : GroundEval R fuel (r.rhs.subst (fun x => (β x).toTerm)) m v) :
      GroundEval R (fuel+1) (.func (.inr f) ts)
        ((((List.finRange n).map costs).sum) + m + 1) v

namespace GroundEval
variable {R : RewriteSystem C D}

theorem mono {k : Nat} {t : Term C D} {m : Nat} {v : Value C}
    (h : GroundEval R k t m v) : ∀ l, k ≤ l → GroundEval R l t m v := by
  induction h with
  | value k v => intro l hl; exact .value l v
  | constructor k c ts costs vs hargs ih =>
    intro l hl
    cases l with
    | zero => omega
    | succ l => exact .constructor l c ts costs vs (fun i => ih i l (by omega))
  | rewrite k f ts costs vs hargs r hr ha hf β hmatch m v hbody ihargs ihbody =>
    intro l hl
    cases l with
    | zero => omega
    | succ l =>
      exact .rewrite l f ts costs vs (fun i => ihargs i l (by omega))
        r hr ha hf β hmatch m v (ihbody l (by omega))

theorem value_inv_aux {k m : Nat} {t : HofmannMoser.Term C D} {w : Value C}
    (h : GroundEval R k t m w) : ∀ v : Value C, t = v.toTerm → m = 0 ∧ w = v := by
  induction h with
  | value k w =>
    intro v heq
    exact ⟨rfl, Value.toTerm_injective heq⟩
  | constructor k c ts costs vs hargs ih =>
    intro v heq
    cases v with
    | node c' ch =>
      cases heq
      have hc : ∀ i, costs i = 0 ∧ vs i = ch i := fun i => ih i (ch i) rfl
      constructor
      · have hcost : costs = fun _ => 0 := funext (fun i => (hc i).1)
        rw [hcost]
        simp
      · congr 1
        exact funext fun i => (hc i).2
  | rewrite k f ts costs vs hargs r hr ha hf β hmatch m v hbody ihargs ihbody =>
    intro w heq
    cases w with
    | node c ch => cases heq

theorem value_inv (v : Value C) {k m : Nat} {w : Value C}
    (h : GroundEval R k v.toTerm m w) : m = 0 ∧ w = v := value_inv_aux h v rfl

/-- Separate a function evaluation into its arguments and a call on their values.
The separated derivations need no additional fuel. -/
theorem split_aux {k m : Nat} {t : HofmannMoser.Term C D} {v : Value C}
    (h : GroundEval R k t m v) :
    ∀ {n : Nat} (f : C n ⊕ D n) (ts : Fin n → HofmannMoser.Term C D), t = .func f ts →
    ∃ (vs : Fin n → Value C) (costs : Fin n → Nat) (outer : Nat),
      (∀ i, GroundEval R k (ts i) (costs i) (vs i)) ∧
      GroundEval R k (.func f (fun i => (vs i).toTerm)) outer v ∧
      m = outer + ((List.finRange n).map costs).sum := by
  induction h with
  | value k v =>
    intro n f ts heq
    cases v with
    | node c ch =>
      cases heq
      exact ⟨ch, fun _ => 0, 0, fun i => .value k (ch i), .value k (.node c ch), by simp⟩
  | constructor k c ts costs vs hargs ih =>
    intro n f args heq
    cases heq
    exact ⟨vs, costs, 0, fun i => (hargs i).mono (k+1) (by omega),
      .value (k+1) (.node c vs), by simp⟩
  | rewrite k f ts costs vs hargs r hr ha hf β hmatch m v hbody ihargs ihbody =>
    intro n f' args heq
    cases heq
    refine ⟨vs, costs, m+1, fun i => (hargs i).mono (k+1) (by omega), ?_, by omega⟩
    simpa using GroundEval.rewrite k f (fun i => (vs i).toTerm) (fun _ => 0) vs
      (fun i => .value k (vs i)) r hr ha hf β hmatch m v hbody

theorem split {k m n : Nat} {v : Value C} {f : C n ⊕ D n}
    {ts : Fin n → HofmannMoser.Term C D} (h : GroundEval R k (.func f ts) m v) :
    ∃ (vs : Fin n → Value C) (costs : Fin n → Nat) (outer : Nat),
      (∀ i, GroundEval R k (ts i) (costs i) (vs i)) ∧
      GroundEval R k (.func f (fun i => (vs i).toTerm)) outer v ∧
      m = outer + ((List.finRange n).map costs).sum := split_aux h f ts rfl

/-- A closed call on values to a defined symbol contains a genuine rewrite;
its body is evaluated with strictly less fuel. -/
theorem defined_inv_aux {k m : Nat} {t : HofmannMoser.Term C D} {v : Value C}
    (h : GroundEval R k t m v) :
    ∀ {n : Nat} (f : D n) (vs : Fin n → Value C),
      t = .func (.inr f) (fun i => (vs i).toTerm) →
    ∃ (fuel : Nat) (r : Rule C D) (ha : r.arity = n) (β : Nat → Value C) (bodyCost : Nat),
      fuel < k ∧ R r ∧ (ha ▸ r.symbol) = f ∧
      (∀ i, (vs i).toTerm = (r.patterns (Fin.cast ha.symm i)).subst (fun x => (β x).toTerm)) ∧
      GroundEval R fuel (r.rhs.subst (fun x => (β x).toTerm)) bodyCost v ∧
      m = bodyCost+1 := by
  induction h with
  | value k v =>
    intro n f vs heq
    cases v with
    | node c ch => cases heq
  | constructor k c ts costs vs hargs ih =>
    intro n f vals heq
    cases heq
  | rewrite k f ts costs vs hargs r hr ha hf β hmatch m v hbody ihargs ihbody =>
    intro n f' vals heq
    cases heq
    have hv : ∀ i, costs i = 0 ∧ vs i = vals i := fun i => value_inv (vals i) (hargs i)
    refine ⟨k, r, ha, β, m, by omega, hr, hf, ?_, hbody, ?_⟩
    · intro i
      simpa only [(hv i).2] using hmatch i
    · have hcost : costs = fun _ => 0 := funext (fun i => (hv i).1)
      rw [hcost]
      simp

theorem defined_inv {k m n : Nat} {f : D n} {vs : Fin n → Value C} {v : Value C}
    (h : GroundEval R k (.func (.inr f) (fun i => (vs i).toTerm)) m v) :
    ∃ (fuel : Nat) (r : Rule C D) (ha : r.arity = n) (β : Nat → Value C) (bodyCost : Nat),
      fuel < k ∧ R r ∧ (ha ▸ r.symbol) = f ∧
      (∀ i, (vs i).toTerm = (r.patterns (Fin.cast ha.symm i)).subst (fun x => (β x).toTerm)) ∧
      GroundEval R fuel (r.rhs.subst (fun x => (β x).toTerm)) bodyCost v ∧
      m = bodyCost+1 := defined_inv_aux h f vs rfl

/-- Substitute completed argument evaluations into a call on their values. -/
theorem compose {k K m n : Nat} {f : C n ⊕ D n} {vs : Fin n → Value C} {v : Value C}
    (h : GroundEval R k (.func f (fun i => (vs i).toTerm)) m v)
    (ts : Fin n → HofmannMoser.Term C D) (costs : Fin n → Nat)
    (hargs : ∀ i, GroundEval R K (ts i) (costs i) (vs i)) (hk : k ≤ K) :
    GroundEval R (K+1) (.func f ts) (m+((List.finRange n).map costs).sum) v := by
  cases f with
  | inl c =>
    obtain ⟨hm, hv⟩ := value_inv (.node c vs) h
    subst m
    subst v
    simpa using GroundEval.constructor K c ts costs vs hargs
  | inr f =>
    obtain ⟨fuel, r, ha, β, bodyCost, hfuel, hr, hf, hmatch, hbody, hm⟩ := defined_inv h
    have hb := hbody.mono K (by omega)
    have hg := GroundEval.rewrite K f ts costs vs hargs r hr ha hf β hmatch bodyCost v hb
    convert hg using 1 <;> omega

end GroundEval
end HMProof

/- Draft section to be incorporated into the soundness solution.
The reroot/run-count calculation follows the accepted proof of Lemma 12 by
Prove2Me contributor fizzyinc3 (submission 1b4ae18a-a20b-4c9b-92a8-ea5da9dbe1bb).
Mathematical source: Hofmann and Moser, TLCA 2015, Lemma 12 and Definition 15.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
-/
namespace HMProof
variable {C D : Nat → Type u}

/-- List form of the finite nonnegative potential sum. -/
def listPotential {n : Nat} (Q : Annotation C n) (vs : List (Value C)) : ℝ≥0∞ :=
  (Q.map (fun e => lift e.2.1 * weight (List.ofFn e.1) vs)).sum

@[simp] theorem listPotential_cast {n m : Nat} (h : n=m) (Q : Annotation C n)
    (vs : List (Value C)) : listPotential (h ▸ Q) vs = listPotential Q vs := by
  subst m
  rfl

theorem listPotential_ofFn {n : Nat} (Q : Annotation C n) (vs : Fin n → Value C) :
    listPotential Q (List.ofFn vs) = lift (potential Q vs) := by
  induction Q with
  | nil => simp [listPotential, potential]
  | cons e Q ih =>
    change lift e.2.1 * weight (List.ofFn e.1) (List.ofFn vs) +
      listPotential Q (List.ofFn vs) =
      lift (e.2.1 * (multivariateBasic e.1 vs : Rat) + potential Q vs)
    rw [weight_ofFn, ih, lift_add (mul_nonneg e.2.2 (Nat.cast_nonneg _)) (potential_nonneg _ _),
      lift_mul e.2.2, lift_nat]

theorem reroot_count (A : TreeAutomaton C) (q : Fin A.stateCount) (v : Value C)
    (s : Fin (A.reroot q).stateCount) :
    (A.reroot q).runCount v s = A.runCount v s := by
  induction v generalizing s with
  | node c ch ih =>
    rw [TreeAutomaton.runCount.eq_1 (A.reroot q), TreeAutomaton.runCount.eq_1 A s]
    congr 1
    apply List.map_congr_left
    intro tr htr
    congr 1
    congr 1
    funext i
    exact ih i (tr.1 i)

theorem basic_node (P : RepPolicy C) {n : Nat} (c : C n) (p : BasicFunction C)
    (vs : Fin n → Value C) :
    p.val (.node c vs) =
      ((((P.rep p).rules n c).filter (fun tr => tr.2 == (P.rep p).final)).map
        (fun tr => multivariateBasic (fun i => BasicFunction.reroot (P.rep p) (tr.1 i)) vs)).sum := by
  rw [← P.rep_basic p]
  unfold TreeAutomaton.basic
  rw [TreeAutomaton.runCount.eq_1]
  congr 1
  apply List.map_congr_left
  intro tr htr
  unfold multivariateBasic
  congr 1
  congr 1
  funext i
  exact (reroot_count (P.rep p) (tr.1 i) (vs i) (tr.1 i)).symm

theorem basic_node_weight (P : RepPolicy C) {n : Nat} (c : C n) (p : BasicFunction C)
    (vs : Fin n → Value C) :
    (p.val (.node c vs) : ℝ≥0∞) =
      ((((P.rep p).rules n c).filter (fun tr => tr.2 == (P.rep p).final)).map
        (fun tr => weight (List.ofFn (fun i => BasicFunction.reroot (P.rep p) (tr.1 i)))
          (List.ofFn vs))).sum := by
  simp_rw [weight_ofFn]
  rw [basic_node P c p vs, Nat.cast_list_sum, List.map_map]
  rfl

theorem list_split {α : Type u} (xs : List α) (i : Nat) (hi : i < xs.length) :
    xs = xs.take i ++ [xs[i]] ++ xs.drop (i+1) := by
  have h := List.take_append_drop i xs
  rw [List.drop_eq_getElem_cons hi] at h
  simpa [List.append_assoc] using h.symm

theorem weight_split (ps : List (BasicFunction C)) (vs : List (Value C)) (i : Nat)
    (hi : i < ps.length) (hlen : ps.length = vs.length) :
    weight ps vs = weight (ps.take i) (vs.take i) * (ps[i].val vs[i] : ℝ≥0∞) *
      weight (ps.drop (i+1)) (vs.drop (i+1)) := by
  have hiv : i < vs.length := by omega
  conv_lhs => rw [list_split ps i hi, list_split vs i hiv]
  rw [weight_append _ _ _ _ (by simp [hlen])]
  rw [weight_append _ _ _ _ (by simp [hlen])]
  simp [weight_singleton, mul_assoc]

theorem weight_replace (ps : List (BasicFunction C)) (vs : List (Value C)) (i : Nat)
    (cs : List (BasicFunction C)) (ws : List (Value C))
    (hi : i < ps.length) (hlen : ps.length = vs.length) (hc : cs.length = ws.length) :
    weight (replaceAt ps i cs) (replaceAt vs i ws) =
      weight (ps.take i) (vs.take i) * weight cs ws *
        weight (ps.drop (i+1)) (vs.drop (i+1)) := by
  unfold replaceAt
  rw [weight_append _ _ _ _ (by simp [hc, hlen])]
  rw [weight_append _ _ _ _ (by simp [hlen])]

/-- Interpreting constructor patterns under a total value environment. -/
def patternValue (β : Nat → Value C) : HofmannMoser.Term C D → Value C
  | .var x => β x
  | .func (.inl c) args => .node c (fun i => patternValue β (args i))
  | .func (.inr _) _ => β 0

theorem patternValue_toTerm (β : Nat → Value C) {t : HofmannMoser.Term C D}
    (h : IsConstructorTerm t) : (patternValue β t).toTerm = t.subst (fun x => (β x).toTerm) := by
  induction h with
  | var x => rfl
  | constructor c args hargs ih =>
    change HofmannMoser.Term.func (.inl c) (fun i => (patternValue β (args i)).toTerm) =
      HofmannMoser.Term.func (.inl c) (fun i => (args i).subst (fun x => (β x).toTerm))
    congr 1
    funext i
    exact ih i

end HMProof

/-!
Constructor-pattern shifts for Hofmann--Moser, Lemma 12 and Definition 15.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
-/
namespace HMProof
variable {C D : Nat → Type u}

@[simp] theorem ofFn_get_length {α : Type u} {n : Nat} (xs : List α)
    (hlen : xs.length = n) :
    List.ofFn (fun i : Fin n => xs[i.val]'(by omega)) = xs := by
  subst n
  exact List.ofFn_get xs

theorem sum_flatMap_map {α : Type u} {β : Type u} (xs : List α) (f : α → List β)
    (g : β → ℝ≥0∞) :
    ((xs.flatMap f).map g).sum = (xs.map (fun x => ((f x).map g).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- Expanding an arbitrary constructor coordinate preserves its potential. -/
theorem listPotential_shiftAt (P : RepPolicy C) {n k : Nat} (pos : Fin n) (c : C k)
    (Q : Annotation C n) (vs : List (Value C)) (hlen : vs.length = n)
    (children : Fin k → Value C) (hnode : vs[pos.val]'(by omega) = .node c children) :
    listPotential (additiveShiftAt P pos c Q)
      (replaceAt vs pos.val (List.ofFn children)) = listPotential Q vs := by
  unfold listPotential additiveShiftAt
  rw [sum_flatMap_map]
  congr 1
  apply List.map_congr_left
  intro entry hentry
  dsimp
  simp only [List.map_map, Function.comp_def]
  have hkeys (cs : Fin k → BasicFunction C) :=
    ofFn_get_length (n := n-1+k) (replaceAt (List.ofFn entry.1) pos.val (List.ofFn cs))
      (by rw [replaceAt_length _ _ _ (by simpa using pos.isLt)]; simp)
  simp_rw [hkeys]
  have hw (cs : Fin k → BasicFunction C) :
      weight (replaceAt (List.ofFn entry.1) pos.val (List.ofFn cs))
        (replaceAt vs pos.val (List.ofFn children)) =
      weight ((List.ofFn entry.1).take pos.val) (vs.take pos.val) *
        weight (List.ofFn cs) (List.ofFn children) *
        weight ((List.ofFn entry.1).drop (pos.val+1)) (vs.drop (pos.val+1)) :=
    weight_replace _ _ _ _ _ (by simpa using pos.isLt) (by simpa using hlen.symm) (by simp)
  simp_rw [hw]
  rw [weight_split (List.ofFn entry.1) vs pos.val (by simpa using pos.isLt)
    (by simpa using hlen.symm)]
  simp only [List.getElem_ofFn, hnode]
  rw [basic_node_weight P c (entry.1 pos) children]
  simp_rw [mul_assoc]
  rw [← List.sum_map_mul_right, ← List.sum_map_mul_left, ← List.sum_map_mul_left]


/-- Potential conservation throughout a left-hand-side constructor expansion. -/
theorem patternExpansion_potential (P : RepPolicy C)
    {patterns : List (HofmannMoser.Term C D)} {Q : Annotation C patterns.length}
    {vars : List Nat} {Q' : Annotation C vars.length}
    (h : PatternExpansion P patterns Q vars Q') (β : Nat → Value C) :
    listPotential Q (patterns.map (patternValue β)) = listPotential Q' (vars.map β) := by
  induction h with
  | done vars Q =>
    simp [List.map_map, Function.comp_def, patternValue]
  | step patterns pos c args hPattern Q vars Q' hNext ih =>
    rw [← ih]
    simp only [listPotential_cast]
    have hmap : (replaceAt patterns pos.val (List.ofFn args)).map (patternValue β) =
        replaceAt (patterns.map (patternValue β)) pos.val
          (List.ofFn (fun i => patternValue β (args i))) := by
      simp only [replaceAt, List.map_append, List.map_take, List.map_drop, List.map_ofFn]
      rfl
    rw [hmap]
    symm
    apply listPotential_shiftAt P pos c Q (patterns.map (patternValue β)) (by simp)
      (fun i => patternValue β (args i))
    simp only [List.getElem_map]
    change patternValue β (patterns.get pos) = _
    rw [hPattern]
    rfl

end HMProof
/-!
Structural resource identities used for Hofmann--Moser, Figure 2.
Uses accepted Lemmas 12 and 13 by Prove2Me contributor fizzyinc3.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
-/
namespace HMProof
variable {C D : Nat → Type u}

theorem multivariateBasic_product {n : Nat} (ps : Fin n → BasicFunction C)
    (vs : Fin n → Value C) : multivariateBasic ps vs = ∏ i, (ps i).val (vs i) := by
  have hfold : ∀ (l : List Nat) (a : Nat), l.foldl (· * ·) a = a * l.prod := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons x l ih => intro a; simp [List.foldl, ih, mul_assoc]
  simp [multivariateBasic, hfold, List.prod_ofFn]

theorem potential_reindex {n : Nat} (ρ : Fin n → Fin n) (hi : Function.Injective ρ)
    (hs : Function.Surjective ρ) (Q : Annotation C n) (vs : Fin n → Value C) :
    potential (annotationReindex ρ Q) (fun i => vs (ρ i)) = potential Q vs := by
  unfold potential annotationReindex
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  dsimp
  congr 2
  rw [multivariateBasic_product, multivariateBasic_product]
  exact Function.Bijective.prod_comp ⟨hi, hs⟩ (fun i => (e.1 i).val (vs i))

theorem potential_addConstant (S : FiniteConstructors C) {n : Nat}
    (Q : Annotation C n) (K : {q : Rat // 0 ≤ q}) (vs : Fin n → Value C) :
    potential (addConstant S Q K) vs = potential Q vs + K.1 := by
  change K.1 * (multivariateBasic (canonicalTuple S n) vs : Rat) + potential Q vs = _
  have hc : multivariateBasic (canonicalTuple S n) vs = 1 := by
    simp [multivariateBasic_product, canonicalTuple, canonical_val]
  rw [hc]
  simp [add_comm]

theorem potential_constructor (P : RepPolicy C) {n : Nat} (c : C n)
    (Q : Annotation C 1) (vs : Fin n → Value C) :
    potential (Nat.zero_add n ▸ additiveShift P (m := 0) c Q) vs =
      potential Q (fun _ => .node c vs) := by
  have h := HofmannMoser.lemma_12 (m := 0) P c Q Fin.elim0 vs
  simpa [Fin.addCases] using h.symm

theorem weight_last {n : Nat} (ps : Fin (n+1) → BasicFunction C)
    (vs : Fin (n+1) → Value C) :
    weight (List.ofFn ps) (List.ofFn vs) =
      weight (List.ofFn (fun i => ps i.castSucc)) (List.ofFn (fun i => vs i.castSucc)) *
        ((ps (Fin.last n)).val (vs (Fin.last n)) : ℝ≥0∞) := by
  conv_lhs => rw [List.ofFn_succ_last (f := ps), List.ofFn_succ_last (f := vs)]
  rw [weight_append _ _ _ _ (by simp), weight_singleton]

/-- Dropping a context coordinate keeps the canonical suffix slice; its potential
is at most the original nonnegative potential. -/
theorem potential_project (S : FiniteConstructors C) {n : Nat} (Q : Annotation C (n+1))
    (vs : Fin (n+1) → Value C) :
    lift (potential (annotationProject Q (canonicalTuple S 1)) (fun i => vs i.castSucc)) ≤
      lift (potential Q vs) := by
  classical
  rw [← listPotential_ofFn, ← listPotential_ofFn]
  induction Q with
  | nil => simp [listPotential, annotationProject]
  | cons e Q ih =>
    by_cases he : (fun i : Fin 1 => e.1 (Fin.natAdd n i)) = canonicalTuple S 1
    · have hc : e.1 (Fin.last n) = BasicFunction.canonical S := by
        simpa [canonicalTuple] using congrFun he 0
      simp only [annotationProject, List.filterMap_cons, if_pos he,
        listPotential, List.map_cons, List.sum_cons] at ih ⊢
      rw [weight_last, hc, canonical_val, Nat.cast_one, mul_one]
      exact add_le_add le_rfl ih
    · simp only [annotationProject, List.filterMap_cons, if_neg he,
        listPotential, List.map_cons, List.sum_cons] at ih ⊢
      simpa only [ENNReal.bot_eq_zero, zero_add] using add_le_add (bot_le : (0 : ℝ≥0∞) ≤
        lift e.2.1 * weight (List.ofFn e.1) (List.ofFn vs)) ih

def updateValues {n : Nat} (xs : Fin n → Nat) (vs : Fin n → Value C)
    (β : Nat → Value C) (x : Nat) : Value C :=
  if h : ∃ i, xs i = x then vs (Classical.choose h) else β x

@[simp] theorem updateValues_apply {n : Nat} (xs : Fin n → Nat) (vs : Fin n → Value C)
    (β : Nat → Value C) (hi : Function.Injective xs) (i : Fin n) :
    updateValues xs vs β (xs i) = vs i := by
  unfold updateValues
  rw [dif_pos ⟨i, rfl⟩]
  congr 1
  apply hi
  exact Classical.choose_spec (⟨i, rfl⟩ : ∃ j, xs j = xs i)

theorem ofFn_list_map (xs : List Nat) (f : Nat → Value C) :
    List.ofFn (fun i => f (xs.get i)) = xs.map f := by
  change List.ofFn (f ∘ xs.get) = xs.map f
  rw [← List.map_ofFn, List.ofFn_get]

/-- The sharing renaming is interpreted by assigning the shared value to both
old variables. -/
theorem sharing_inputs (β : Nat → Value C) {n : Nat} (xs : Fin n → Nat) (x y z : Nat)
    (hFresh : ∀ i, xs i ≠ x ∧ xs i ≠ y ∧ xs i ≠ z) :
    (fun i : Fin (n+2) => β ((fun v : Nat => if v=x ∨ v=y then z else v)
      ((Fin.addCases xs (fun i : Fin 2 => if i.val=0 then x else y) : Fin (n+2) → Nat) i))) =
    (Fin.addCases (fun i => β (xs i)) (fun _ : Fin 2 => β z) : Fin (n+2) → Value C) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [(hFresh j).1, (hFresh j).2.1]
  · intro j
    by_cases hj : j = 0 <;> simp [hj]

theorem sharing_outputs (β : Nat → Value C) {n : Nat} (xs : Fin n → Nat) (z : Nat) :
    (fun i : Fin (n+1) => β ((Fin.addCases xs (fun _ : Fin 1 => z) : Fin (n+1) → Nat) i)) =
      (Fin.addCases (fun i => β (xs i)) (fun _ : Fin 1 => β z) : Fin (n+1) → Value C) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

end HMProof

/-!
Soundness of resource typing, following Hofmann--Moser, Theorem 16.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
-/
namespace HMProof
variable {C D : Nat → Type u}

@[simp] theorem charge_zero (mode : TypingMode) : charge mode 0 = 0 := by
  cases mode <;> simp [charge]

@[simp] theorem charge_add (mode : TypingMode) (a b : Nat) :
    charge mode (a+b) = charge mode a + charge mode b := by
  cases mode <;> simp [charge]

def SoundAt (R : RewriteSystem C D) (fuel : Nat) (mode : TypingMode) {n : Nat}
    (xs : Fin n → Nat) (Q : Annotation C n) (t : HofmannMoser.Term C D)
    (Q' : Annotation C 1) : Prop :=
  ∀ (β : Nat → Value C) (m : Nat) (v : Value C),
    GroundEval R fuel (t.subst (fun x => (β x).toTerm)) m v →
    lift (potential Q' (fun _ => v)) + charge mode m ≤
      lift (potential Q (fun i => β (xs i)))

/-- Boundedness supplies precisely the resource needed for a defined-function
rewrite and for its recursively evaluated right-hand side. -/
theorem bounded_defined (S : FiniteConstructors C) (P : RepPolicy C)
    (F : AnnotatedSignatures C D) (R : RewriteSystem C D)
    (hRules : LeftLinearConstructorSystem R) (hBounded : BoundedSignatures S P F R)
    (fuel : Nat)
    (hIH : ∀ k, k < fuel → ∀ {mode : TypingMode} {n : Nat} {xs : Fin n → Nat}
      {Q : Annotation C n} {t : HofmannMoser.Term C D} {Q' : Annotation C 1},
      Typing S P F mode n xs Q t Q' → SoundAt R k mode xs Q t Q')
    {mode : TypingMode} {n : Nat} (f : D n) (xs : Fin n → Nat)
    (Q : Annotation C n) (Q' : Annotation C 1) (hSig : F.get mode n f Q Q') :
    SoundAt R fuel mode xs Q (.func (.inr f) (fun i => .var (xs i))) Q' := by
  intro β m v heval
  obtain ⟨k, r, ha, γ, bodyCost, hk, hr, hf, hmatch, hbody, hm⟩ := GroundEval.defined_inv heval
  subst n
  subst f
  have hbmode : Bounded S P F R mode := by
    cases mode with
    | counted => exact hBounded.1
    | costFree => exact hBounded.2
  obtain ⟨vars, P0, shifted, hExpand, hCredit, hType⟩ := hbmode r hr Q Q' hSig
  have hvals : ∀ i, β (xs i) = patternValue γ (r.patterns i) := by
    intro i
    apply Value.toTerm_injective
    exact (hmatch i).trans (patternValue_toTerm γ ((hRules r hr).1 i)).symm
  have hExpansion := patternExpansion_potential P hExpand γ
  rw [listPotential_cast] at hExpansion
  have hl : (List.ofFn r.patterns).map (patternValue γ) = List.ofFn (fun i => β (xs i)) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact (hvals i).symm
  rw [hl, ← ofFn_list_map vars γ, listPotential_ofFn, listPotential_ofFn] at hExpansion
  have hCreditPot : lift (potential P0 (fun i => γ (vars.get i))) + charge mode 1 =
      lift (potential shifted (fun i => γ (vars.get i))) := by
    cases mode with
    | counted =>
      have hc := potential_eq hCredit (fun i => γ (vars.get i))
      rw [potential_addConstant] at hc
      rw [← hc]
      simp only [onePotential, charge_counted, Nat.cast_one]
      rw [lift_add (potential_nonneg _ _) (by decide : (0 : Rat) ≤ 1), lift_one]
    | costFree =>
      rw [charge_costFree, add_zero]
      exact congrArg lift (potential_eq hCredit (fun i => γ (vars.get i)))
  have hbodyPot := hIH k hk hType γ bodyCost v hbody
  rw [hm, charge_add]
  calc
    _ = (lift (potential Q' (fun _ => v)) + charge mode bodyCost) + charge mode 1 := by ac_rfl
    _ ≤ lift (potential P0 (fun i => γ (vars.get i))) + charge mode 1 := add_le_add hbodyPot le_rfl
    _ = lift (potential shifted (fun i => γ (vars.get i))) := hCreditPot
    _ = lift (potential Q (fun i => β (xs i))) := hExpansion.symm

end HMProof
/-!
The composition case of Hofmann--Moser typing soundness.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
-/
namespace HMProof
variable {C D : Nat → Type u}

theorem composition_sound (S : FiniteConstructors C) (R : RewriteSystem C D)
    (fuel : Nat) (mode : TypingMode) (last : Nat) (f : C (last+1) ⊕ D (last+1))
    (contexts : Nat → List Nat) (terms : Nat → HofmannMoser.Term C D)
    (fresh : Fin (last+1) → Nat) (hFreshInj : Function.Injective fresh)
    (Q : Annotation C (argumentContexts contexts (last+1)).length)
    (S' : Annotation C (last+1)) (Q' : Annotation C 1)
    (P : (i : Nat) → List (BasicFunction C) → Annotation C (contexts i).length)
    (U : Nat → List (BasicFunction C) → Annotation C 1)
    (hcoef : compositionCoefficients last (fun i => (contexts i).length)
      (argumentContexts_length contexts (last+1) ▸ Q) S' P U)
    (hArgs : ∀ i, i < last+1 → ∀ ps,
      ps.length = i+contextWidth (fun j => (contexts j).length) (i+1) (last+1) →
      SoundAt R fuel (listPremiseMode S mode ps) (contexts i).get (P i ps) (terms i) (U i ps))
    (hFun : SoundAt R fuel mode fresh S' (.func f (fun i => .var (fresh i))) Q') :
    SoundAt R fuel mode (argumentContexts contexts (last+1)).get Q
      (.func f (fun i => terms i.val)) Q' := by
  intro β m v heval
  obtain ⟨vs, costs, outer, hEvalArgs, hEvalOuter, hm⟩ := GroundEval.split heval
  let γ := updateValues fresh vs β
  have hEvalFunction : GroundEval R fuel
      ((.func f (fun i => .var (fresh i)) : HofmannMoser.Term C D).subst
        (fun x => (γ x).toTerm)) outer v := by
    simpa only [HofmannMoser.Term.subst, γ, updateValues_apply fresh vs β hFreshInj] using hEvalOuter
  have hFunction := hFun γ outer v hEvalFunction
  simp only [γ, updateValues_apply fresh vs β hFreshInj] at hFunction
  let values := fun i (j : Fin (contexts i).length) => β ((contexts i).get j)
  let outputs := fun i => if h : i < last+1 then vs ⟨i,h⟩ else β 0
  let costsN := fun i => if h : i < last+1 then costs ⟨i,h⟩ else 0
  let heq := argumentContexts_length contexts (last+1)
  let Q0 : Annotation C (contextWidth (fun i => (contexts i).length) 0 (last+1)) := heq ▸ Q
  let all : Fin (contextWidth (fun i => (contexts i).length) 0 (last+1)) → Value C :=
    fun i => β ((argumentContexts contexts (last+1)).get (Fin.cast heq.symm i))
  have hall : List.ofFn all = valueBlocks (fun i => List.ofFn (values i)) 0 (last+1) := by
    dsimp only [all, values]
    rw [ofFn_cast heq.symm (fun j => β ((argumentContexts contexts (last+1)).get j)), ofFn_list_map]
    simp only [argumentContexts, List.map_flatMap, valueBlocks, Nat.sub_zero, Nat.zero_add]
    apply congrArg (fun g : Nat → List (Value C) => (List.range (last+1)).flatMap g)
    funext i
    apply List.ext_getElem <;> simp
  have hInputs : ∀ i, i < last+1 → ∀ ps,
      ps.length = i+contextWidth (fun j => (contexts j).length) (i+1) (last+1) →
      lift (potential (U i ps) (fun _ => outputs i)) +
        charge (listPremiseMode S mode ps) (costsN i) ≤ lift (potential (P i ps) (values i)) := by
    intro i hi ps hp
    have h := hArgs i hi ps hp β (costs ⟨i,hi⟩) (vs ⟨i,hi⟩) (hEvalArgs ⟨i,hi⟩)
    simpa only [values, outputs, costsN, dif_pos hi] using h
  have hCombined := composition_potential S mode last (fun i => (contexts i).length)
    Q0 S' P U hcoef values outputs costsN all hall hInputs
  have houtputs : (fun i : Fin (last+1) => outputs i.val) = vs := by
    funext i
    simp only [outputs, dif_pos i.isLt]
  have hcosts : ((List.range (last+1)).map costsN).sum =
      ((List.finRange (last+1)).map costs).sum := by
    rw [← ofFn_nat costsN (last+1)]
    have he : (fun i : Fin (last+1) => costsN i.val) = costs := by
      funext i
      simp only [costsN, dif_pos i.isLt]
    rw [he, List.ofFn_eq_map]
  have hinput : potential Q0 all = potential Q (fun i => β ((argumentContexts contexts (last+1)).get i)) := by
    simp [Q0, all]
  rw [houtputs, hcosts, hinput] at hCombined
  rw [hm, charge_add]
  calc
    _ = (lift (potential Q' (fun _ => v)) + charge mode outer) +
        charge mode (((List.finRange (last+1)).map costs).sum) := by ac_rfl
    _ ≤ lift (potential S' vs) + charge mode (((List.finRange (last+1)).map costs).sum) :=
      add_le_add hFunction le_rfl
    _ ≤ _ := hCombined

end HMProof
/-!
Simultaneous counted/cost-free typing soundness for Hofmann--Moser.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
-/
namespace HMProof
variable {C D : Nat → Type u}

theorem typing_sound (S : FiniteConstructors C) (P : RepPolicy C)
    (F : AnnotatedSignatures C D) (R : RewriteSystem C D)
    (hRules : LeftLinearConstructorSystem R) (hBounded : BoundedSignatures S P F R) :
    ∀ fuel, ∀ {mode : TypingMode} {n : Nat} {xs : Fin n → Nat}
      {Q : Annotation C n} {t : HofmannMoser.Term C D} {Q' : Annotation C 1},
      Typing S P F mode n xs Q t Q' → SoundAt R fuel mode xs Q t Q' := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel hFuel =>
    intro mode n xs Q t Q' hType
    induction hType with
    | «variable» mode x Q =>
      intro β m v heval
      obtain ⟨hm, hv⟩ := GroundEval.value_inv (β x) heval
      subst m
      subst v
      simp [charge]
    | defined mode f xs Q Q' hDistinct hannotated =>
      exact bounded_defined S P F R hRules hBounded fuel hFuel f xs Q Q' hannotated
    | constructor mode c xs Q hDistinct =>
      intro β m v heval
      obtain ⟨hm, hv⟩ := GroundEval.value_inv (.node c (fun i => β (xs i))) heval
      subst m
      subst v
      simp only [charge_zero, add_zero]
      rw [potential_constructor]
    | weakenAnnotations mode xs P0 Q P' Q' t hDistinct h hInput hOutput ih =>
      intro β m v heval
      calc
        _ ≤ lift (potential P' (fun _ => v)) + charge mode m :=
          add_le_add (lift_mono (potential_mono hOutput _)) le_rfl
        _ ≤ lift (potential P0 (fun i => β (xs i))) := ih β m v heval
        _ ≤ _ := lift_mono (potential_mono hInput _)
    | exchange mode xs ρ hInjective hSurjective Q Q' t h ih =>
      intro β m v heval
      rw [potential_reindex ρ hInjective hSurjective Q (fun i => β (xs i))]
      exact ih β m v heval
    | weakenContext mode xs Q Q' t hDistinct h ih =>
      intro β m v heval
      exact (ih β m v heval).trans (potential_project S Q (fun i => β (xs i)))
    | share mode xs x y z Q Q' t hContext hDistinct hFresh hNew h ih =>
      intro β m v heval
      let ren : Nat → Nat := fun x' => if x'=x ∨ x'=y then z else x'
      let γ := fun x' => β (ren x')
      have heval' : GroundEval R fuel (t.subst (fun x' => (γ x').toTerm)) m v := by
        simpa only [HofmannMoser.Term.rename, Term.subst_subst, HofmannMoser.Term.subst, γ, ren]
          using heval
      have hb := ih γ m v heval'
      change lift (potential Q' (fun _ => v)) + charge mode m ≤
        lift (potential Q (fun i => β ((fun x' => if x'=x ∨ x'=y then z else x')
          ((Fin.addCases xs (fun i : Fin 2 => if i.val=0 then x else y) :
            Fin (_+2) → Nat) i)))) at hb
      rw [sharing_inputs β xs x y z hFresh] at hb
      rw [sharing_outputs β xs z]
      rw [← HofmannMoser.lemma_13 S P Q (fun i => β (xs i)) (β z)]
      exact hb
    | composition mode last f contexts terms fresh Q S' Q' P_arg R_arg
        hContexts hCoverage hDistinct hFresh hCoefficients hArguments hFunction ihArgs ihFunction =>
      exact composition_sound S R fuel mode last f contexts terms fresh hDistinct Q S' Q'
        P_arg R_arg hCoefficients ihArgs ihFunction

end HMProof

/-!
Relating substitution-based evaluation to closed evaluation, Hofmann--Moser Figure 1.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
-/
namespace HMProof
variable {C D : Nat → Type u}

def normalValues (σ : Substitution C D) (hnorm : σ.Normalised) (β : Nat → Value C)
    (x : Nat) : Value C :=
  if hx : x ∈ σ.dom then Classical.choose (Value.exists_of_isValue (hnorm x hx)) else β x

theorem normalValues_toTerm (σ : Substitution C D) (hnorm : σ.Normalised)
    (β : Nat → Value C) (x : Nat) (hx : x ∈ σ.dom) :
    (normalValues σ hnorm β x).toTerm = σ.assignment x := by
  unfold normalValues
  rw [dif_pos hx]
  exact Classical.choose_spec (Value.exists_of_isValue (hnorm x hx))

@[simp] theorem normalValues_out (σ : Substitution C D) (hnorm : σ.Normalised)
    (β : Nat → Value C) (x : Nat) (hx : x ∉ σ.dom) : normalValues σ hnorm β x = β x := by
  unfold normalValues
  rw [dif_neg hx]

theorem instantiate_value_coverage (σ : Substitution C D) (t : HofmannMoser.Term C D) :
    IsValue (σ.instantiate t) → ∀ x ∈ t.variables, x ∈ σ.dom := by
  induction t with
  | var x =>
    intro hv y hy
    have hxy : y=x := by simpa [HofmannMoser.Term.variables] using hy
    subst y
    by_cases hx : x ∈ σ.dom
    · exact hx
    · have hbad : IsValue (.var x : HofmannMoser.Term C D) := by
        simpa [Substitution.instantiate, Substitution.apply, HofmannMoser.Term.subst, hx] using hv
      cases hbad
  | func f args ih =>
    intro hv x hx
    simp only [HofmannMoser.Term.variables, List.mem_flatMap, List.mem_finRange, true_and] at hx
    obtain ⟨i, hi⟩ := hx
    have hargs : ∀ j, IsValue (σ.instantiate (args j)) := by
      cases f with
      | inl c => cases hv with | constructor c args hargs => exact hargs
      | inr f => cases hv
    exact ih i (hargs i) x hi

theorem instantiate_values (σ : Substitution C D) (β : Nat → Value C)
    (hAgree : ∀ x ∈ σ.dom, (β x).toTerm = σ.assignment x)
    (t : HofmannMoser.Term C D) (hCov : ∀ x ∈ t.variables, x ∈ σ.dom) :
    σ.instantiate t = t.subst (fun x => (β x).toTerm) := by
  apply Term.subst_congr_on
  intro x hx
  rw [Substitution.apply, if_pos (hCov x hx)]
  exact (hAgree x (hCov x hx)).symm

theorem arguments_assignment {n : Nat} (xs : Fin n → Nat) (raw : Fin n → HofmannMoser.Term C D)
    (hinj : Function.Injective xs) (i : Fin n) :
    (Substitution.arguments xs raw).assignment (xs i) = raw i := by
  dsimp only [Substitution.arguments]
  rw [dif_pos ⟨i,rfl⟩]
  congr 1
  apply hinj
  exact Classical.choose_spec (⟨i,rfl⟩ : ∃ j, xs j = xs i)

/-- Every platform evaluation under a value environment has a closed evaluation
with the same cost and the same constructor result. -/
theorem evaluates_ground {R : RewriteSystem C D} {σ : Substitution C D}
    {t : HofmannMoser.Term C D} {m : Nat} {raw : HofmannMoser.Term C D}
    (h : Evaluates R σ t m raw) :
    ∀ (β : Nat → Value C), (∀ x ∈ σ.dom, (β x).toTerm = σ.assignment x) →
    ∃ (fuel : Nat) (v : Value C), raw = v.toTerm ∧
      GroundEval R fuel (t.subst (fun x => (β x).toTerm)) m v := by
  induction h with
  | var σ x raw hx hv =>
    intro β hAgree
    refine ⟨0, β x, ?_, GroundEval.value 0 (β x)⟩
    exact hv.symm.trans (hAgree x hx).symm
  | constructor σ c xs raw hx hv =>
    intro β hAgree
    refine ⟨0, .node c (fun i => β (xs i)), ?_, GroundEval.value 0 (.node c (fun i => β (xs i)))⟩
    change HofmannMoser.Term.func (.inl c) raw =
      HofmannMoser.Term.func (.inl c) (fun i => (β (xs i)).toTerm)
    congr 1
    funext i
    exact (hv i).symm.trans (hAgree (xs i) (hx i)).symm
  | rewrite σ τ f xs r hr ha hf ρ hrenaming hmatch hdisjoint hnorm m raw heval ih =>
    intro β hAgree
    let δ := normalValues τ hnorm β
    have hδ : ∀ x ∈ τ.dom, (δ x).toTerm = τ.assignment x :=
      normalValues_toTerm τ hnorm β
    have hUnion : ∀ x ∈ (σ.union τ).dom, (δ x).toTerm = (σ.union τ).assignment x := by
      intro x hx
      by_cases hs : x ∈ σ.dom
      · have ht : x ∉ τ.dom := hdisjoint x hs
        simp only [Substitution.union, if_pos hs]
        rw [show δ x = β x from normalValues_out τ hnorm β x ht]
        exact hAgree x hs
      · have ht : x ∈ τ.dom := by simpa only [Substitution.union, List.mem_append, hs, false_or] using hx
        simp only [Substitution.union, if_neg hs]
        exact hδ x ht
    obtain ⟨k, v, hv, hbody⟩ := ih δ hUnion
    let γ := fun x => δ (ρ x)
    have hmatchGround : ∀ i, (β (xs i)).toTerm =
        (r.patterns (Fin.cast ha.symm i)).subst (fun x => (γ x).toTerm) := by
      intro i
      let pat := (r.patterns (Fin.cast ha.symm i)).rename ρ
      have hpval : IsValue (τ.instantiate pat) := by
        rw [← (hmatch i).2, ← hAgree (xs i) (hmatch i).1]
        exact Value.toTerm_isValue _
      have hCov := instantiate_value_coverage τ pat hpval
      have hInstantiation := instantiate_values τ δ hδ pat hCov
      calc
        (β (xs i)).toTerm = σ.assignment (xs i) := hAgree _ (hmatch i).1
        _ = τ.instantiate pat := (hmatch i).2
        _ = pat.subst (fun x => (δ x).toTerm) := hInstantiation
        _ = _ := by
          simp only [pat, HofmannMoser.Term.rename, Term.subst_subst, HofmannMoser.Term.subst, γ]
    have hb : GroundEval R k (r.rhs.subst (fun x => (γ x).toTerm)) m v := by
      simpa only [HofmannMoser.Term.rename, Term.subst_subst, HofmannMoser.Term.subst, γ] using hbody
    refine ⟨k+1, v, hv, ?_⟩
    simpa [HofmannMoser.Term.subst] using
      GroundEval.rewrite k f (fun i => (β (xs i)).toTerm) (fun _ => 0)
        (fun i => β (xs i)) (fun i => GroundEval.value k (β (xs i))) r hr ha hf γ
        hmatchGround m v hb
  | composition σ f ts xs raw costs outerCost rawResult hinj hfresh hfreshTerm hargs houter ihargs ihouter =>
    intro β hAgree
    let fuels := fun i => Classical.choose (ihargs i β hAgree)
    let vals := fun i => Classical.choose (Classical.choose_spec (ihargs i β hAgree))
    have hVals : ∀ i, raw i = (vals i).toTerm := fun i =>
      (Classical.choose_spec (Classical.choose_spec (ihargs i β hAgree))).1
    have hArgs : ∀ i, GroundEval R (fuels i) ((ts i).subst (fun x => (β x).toTerm))
        (costs i) (vals i) := fun i =>
      (Classical.choose_spec (Classical.choose_spec (ihargs i β hAgree))).2
    let γ := updateValues xs vals β
    have hUnion : ∀ x ∈ (σ.union (Substitution.arguments xs raw)).dom,
        (γ x).toTerm = (σ.union (Substitution.arguments xs raw)).assignment x := by
      intro x hx
      by_cases hs : x ∈ σ.dom
      · have hnot : ¬ ∃ i, xs i = x := by
          rintro ⟨i,rfl⟩
          exact hfresh i hs
        simp only [γ, updateValues, dif_neg hnot, Substitution.union, if_pos hs]
        exact hAgree x hs
      · have ht : x ∈ (Substitution.arguments xs raw).dom := by
          simpa only [Substitution.union, List.mem_append, hs, false_or] using hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
        simp only [Substitution.union, if_neg hs, γ, updateValues_apply xs vals β hinj,
          arguments_assignment xs raw hinj]
        exact (hVals i).symm
    obtain ⟨k, v, hv, hOuter⟩ := ihouter γ hUnion
    have hCall : GroundEval R k (.func f (fun i => (vals i).toTerm)) outerCost v := by
      simpa only [HofmannMoser.Term.subst, γ, updateValues_apply xs vals β hinj] using hOuter
    let K := max k (Finset.univ.sup fuels)
    have hArgsK : ∀ i, GroundEval R K ((ts i).subst (fun x => (β x).toTerm)) (costs i) (vals i) := by
      intro i
      apply (hArgs i).mono
      exact (Finset.le_sup (f := fuels) (Finset.mem_univ i)).trans (le_max_right _ _)
    refine ⟨K+1, v, hv, ?_⟩
    exact GroundEval.compose hCall (fun i => (ts i).subst (fun x => (β x).toTerm)) costs
      hArgsK (le_max_left _ _)

end HMProof

/-!
Theorem 16 of Martin Hofmann and Georg Moser, TLCA 2015, pp. 252--253.
Uses their potential method and the accepted platform Lemmas 12 and 13.
The list-based reroot calculation above follows fizzyinc3's accepted Lemma 12
submission 1b4ae18a-a20b-4c9b-92a8-ea5da9dbe1bb.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account
**Victorized**, with assistance from OpenAI Codex.
-/
open HMProof

theorem solution {C D : Nat → Type u}
    (S : FiniteConstructors C) (P : RepPolicy C)
    (F : AnnotatedSignatures C D) (R : RewriteSystem C D)
    (hFinSig : FiniteSignature C D)
    (hFinSys : FiniteSystem R)
    (hOrth : SyntacticallyOrthogonal R)
    (hCompDef : CompletelyDefined R)
    (hExtCounted : AnnotatedSignatureExtensional F.counted)
    (hExtCostFree : AnnotatedSignatureExtensional F.costFree)
    (hBounded : BoundedSignatures S P F R)
    {n : Nat} (xs : Fin n → Nat) (hDistinct : Function.Injective xs)
    (Q : Annotation C n) (t : HofmannMoser.Term C D) (Q' : Annotation C 1)
    (hType : Typing S P F .counted n xs Q t Q')
    (σ : Substitution C D) (hNorm : σ.Normalised)
    (vs : Fin n → Value C)
    (hDom : ∀ i, xs i ∈ σ.dom)
    (hSubst : ∀ i, σ.assignment (xs i) = (vs i).toTerm)
    (m : Nat) (v : Value C)
    (hEval : Evaluates R σ t m v.toTerm) :
    potential Q vs - potential Q' (fun _ ↦ v) ≥ (m : Rat) := by
  let β := normalValues σ hNorm (fun _ => v)
  have hAgree : ∀ x ∈ σ.dom, (β x).toTerm = σ.assignment x := normalValues_toTerm σ hNorm _
  obtain ⟨fuel, w, hw, heval⟩ := evaluates_ground hEval β hAgree
  have hv : v = w := Value.toTerm_injective hw
  subst w
  have hInputs : (fun i => β (xs i)) = vs := by
    funext i
    apply Value.toTerm_injective
    exact (hAgree (xs i) (hDom i)).trans (hSubst i)
  have hb := typing_sound S P F R hOrth.1 hBounded fuel hType β m v heval
  rw [hInputs, charge_counted] at hb
  have hRat : potential Q' (fun _ => v) + (m : Rat) ≤ potential Q vs := by
    apply (lift_le_iff (add_nonneg (potential_nonneg _ _) (Nat.cast_nonneg _))
      (potential_nonneg _ _)).mp
    rw [lift_add (potential_nonneg _ _) (Nat.cast_nonneg _), lift_nat]
    exact hb
  linarith
