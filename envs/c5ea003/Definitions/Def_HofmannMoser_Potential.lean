-- Prove2me | Definitions.Def_HofmannMoser_Potential
-- name    : HofmannMoser_Potential
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-28T00:50:44.185185+00:00
-- url     : https://prove2.me/theorems/7cfe716e-e7ff-4f72-928c-cad874320601
-- title:
--   Tree automata, basic resource functions, and resource potentials
-- statement:
--   Bottom-up nondeterministic tree automata, basic resource functions, and multivariate resource potentials (Sections 2–3, pp. 244–249).
--
--   A ground constructor value $v \in \mathsf{Val}$ (`Value C`) is a constructor tree $c(v_1, \dots, v_n)$ of size $|v| = 1 + \sum_{i=1}^n |v_i|$ (`Value.size`), embedded injectively into first-order terms via `Value.toTerm`. A bottom-up nondeterministic tree automaton $A$ (`TreeAutomaton C`) over a finite nonempty constructor signature (`FiniteConstructors C`) has state space $\operatorname{Fin}(q)$, a designated final state $q_f$, and duplicate-free transition rules $c(q_1, \dots, q_n) \to q$. Its run-count function (`A.runCount v q`) counts bottom-up runs on $v$ ending at $q$:
--
--   $$\operatorname{runCount}_A(c(v_1, \dots, v_n), q) = \sum_{((q_1, \dots, q_n), q) \in \Delta_A(c)} \prod_{i=1}^n \operatorname{runCount}_A(v_i, q_i),$$
--
--   and its basic resource function (Definition 2, p. 245) is $p_A(v) = \operatorname{runCount}_A(v, q_f)$ (`A.basic`).
--
--   The type of basic resource functions is $\mathsf{BF} = \{f : \mathsf{Val} \to \mathbb{N} \mid \exists A,\, p_A = f\}$ (`BasicFunction C`), accompanied by a representative policy $P$ (`RepPolicy C`) selecting one representative automaton $P.\mathrm{rep}(p)$ for each $p \in \mathsf{BF}$ (modeling the fixed enumeration $\mathfrak{A}$ of Section 3, p. 246). Standard operations on $\mathsf{BF}$ include the canonical one-state function $\emptyset$ (`BasicFunction.canonical`), rerooting $p_{(A, q)}$ (`BasicFunction.reroot`), and the Cartesian-product basic function (`BasicFunction.product`).
--
--   For an $n$-tuple $p = (p_1, \dots, p_n) \in \mathsf{BF}^n$, the multivariate basic function (Definition 8, p. 247) is $p(v_1, \dots, v_n) = \prod_{i=1}^n p_i(v_i)$ (`multivariateBasic`). A resource annotation $Q$ of length $n$ (`Annotation C n`) is a finite list of pairs $(p, w)$ with $p \in \mathsf{BF}^n$ and $w \in \mathbb{Q}_{\ge 0}$, inducing the potential (Definitions 5 and 10, pp. 246, 248)
--
--   $$\Phi(v_1, \dots, v_n : Q) = \sum_{(p, w) \in Q} w \cdot p(v_1, \dots, v_n).$$
--
--   This module also defines the class $\mathsf{RF}$ of unary resource functions (`IsResourceFunction`), constant addition $Q + K$ (`addConstant`), coordinate projection $\pi_l^{B_1, \dots, B_m}(Q)$ (`annotationProject`), the additive constructor shift $\triangleleft_c(Q)$ (`additiveShift`, Definition 11, p. 248), and the variable-sharing operator $\Upsilon(Q)$ (`annotationShare`, Lemma 13, p. 249).
--
--   **Formalization Note** To ensure that `TreeAutomaton.product` always satisfies the nonemptiness invariant `has_rule` even when factor automata have disjoint rule supports, the product state space $\operatorname{Fin}(q_A q_B + 1)$ reserves its last index as an unreachable padding state equipped with a self-loop for each constructor.
-- source:
--   Hofmann--Moser 2015, Multivariate Amortised Resource Analysis for Term Rewrite Systems, TLCA 2015, https://doi.org/10.4230/LIPIcs.TLCA.2015.241, Sections 2--3, pp. 244--249, Definitions 2, 5, 8, 10, 11

import Definitions.Def_HofmannMoser_Syntax

/-!
# Tree automata, basic resource functions, and resource potentials

Definitions for Sections 2–3 (Definitions 2, 5, 8, 10, and 11; Propositions 3 and 4;
Lemmas 7, 9, 12, and 13) of Martin Hofmann and Georg Moser, *Multivariate Amortised
Resource Analysis for Term Rewrite Systems*, TLCA 2015, pp. 244–249,
<https://doi.org/10.4230/LIPIcs.TLCA.2015.241>.

Each bottom-up nondeterministic tree automaton `A` defines a basic resource function
`A.basic : Value C → Nat` counting accepting runs on ground constructor values (Definition 2).
Because language-equivalent nondeterministic automata need not have equal accepting-run counts,
and distinct state spaces with equal run-count functions can produce different child transition
decompositions when shifted, resource annotations are indexed by basic functions
`BasicFunction C` (`{f : Value C → Nat // IsBasicFunction C f}`) together with a fixed
representative policy `RepPolicy C` selecting one representative automaton `P.rep p` for each
basic function `p` (representing the paper's fixed enumeration `𝔄`). Annotations are stored
as finite lists of weighted basic-function tuples whose duplicate keys contribute additively
to the coefficient family.
-/

namespace HofmannMoser

universe u

/-- A ground constructor term, with the arity tracked by the constructor's index. -/
inductive Value (C : Nat → Type u) where
  | node {n : Nat} (c : C n) (children : Fin n → Value C) : Value C

/-- A finite nonempty constructor signature, as required in §2 of the paper. The list is
only an enumeration; duplicates do not introduce additional constructors. -/
structure FiniteConstructors (C : Nat → Type u) where
  symbols : List (Sigma C)
  contains : ∀ n (c : C n), Sigma.mk n c ∈ symbols
  nonempty : ∃ n, Nonempty (C n)

namespace Value

/-- The size `|v|` of a ground constructor value is the number of constructor symbols
occurring in `v` (§2, p. 244). -/
def size {C : Nat → Type u} : Value C → Nat
  | .node _ children => 1 + (List.ofFn fun i ↦ (children i).size).sum

/-- Embed a constructor-only ground tree into the paper's full first-order term syntax. -/
def toTerm {C D : Nat → Type u} : Value C → Term C D
  | .node c children => .func (.inl c) fun i ↦ (children i).toTerm

/-- The embedding of a constructor-only ground tree is a value in the term syntax. -/
theorem toTerm_isValue {C D : Nat → Type u} (v : Value C) : IsValue (v.toTerm (D := D)) := by
  cases v with
  | node c children =>
    apply IsValue.constructor
    intro i
    exact toTerm_isValue (children i)

/-- Every constructor-only ground term has a representation by a `Value` tree. -/
theorem exists_of_isValue {C D : Nat → Type u} {t : Term C D} (ht : IsValue t) :
    ∃ v : Value C, v.toTerm (D := D) = t := by
  induction ht with
  | constructor c args _ ih =>
    let values := fun i ↦ Classical.choose (ih i)
    refine ⟨.node c values, ?_⟩
    simp only [toTerm]
    congr 1
    funext i
    exact Classical.choose_spec (ih i)

/-- The embedding `Value.toTerm` is injective. -/
theorem toTerm_injective {C D : Nat → Type u} :
    Function.Injective (Value.toTerm (C := C) (D := D)) := by
  intro v₁
  induction v₁ with
  | node c₁ children₁ ih =>
    intro v₂ h
    cases v₂ with
    | node c₂ children₂ =>
      simp only [toTerm] at h
      injection h with hlen hsum hargs
      subst hlen
      injection hsum with hc
      subst hc
      have hchildren : (fun i ↦ (children₁ i).toTerm (D := D)) =
          (fun i ↦ (children₂ i).toTerm (D := D)) := eq_of_heq hargs
      congr 1
      funext i
      exact ih i (congrFun hchildren i)

end Value

/-- A finite bottom-up nondeterministic tree automaton with one designated final state.
The rules for each constructor form a set, so repeated transitions cannot count twice.
`finite_rules` asserts finiteness even if the ambient constructor family is infinite. -/
structure TreeAutomaton (C : Nat → Type u) where
  stateCount : Nat
  final : Fin stateCount
  rules : (n : Nat) → C n → List ((Fin n → Fin stateCount) × Fin stateCount)
  no_duplicate_rules : ∀ n c, (rules n c).Nodup
  finite_rules : ∃ support : List (Sigma C),
    ∀ n (c : C n), (rules n c).length > 0 → Sigma.mk n c ∈ support
  has_rule : ∃ (n : Nat) (c : C n), (rules n c).length > 0

namespace TreeAutomaton

variable {C : Nat → Type u}

/-- The canonical one-state automaton `∅` has one transition for each constructor.
Every constructor value has exactly one accepting run in it (Definition 2, p. 245). -/
def canonical (S : FiniteConstructors C) : TreeAutomaton C where
  stateCount := 1
  final := 0
  rules := fun _ _ ↦ [(fun _ ↦ 0, 0)]
  no_duplicate_rules := by intro n c; simp
  finite_rules := by
    refine ⟨S.symbols, ?_⟩
    intro n c _
    exact S.contains n c
  has_rule := by
    obtain ⟨n, ⟨c⟩⟩ := S.nonempty
    exact ⟨n, c, by simp⟩

/-- The automaton `(A, q)` obtained from `A` by replacing its designated final state with `q`
(§2, p. 245). -/
def reroot (A : TreeAutomaton C) (q : Fin A.stateCount) : TreeAutomaton C :=
  { A with final := q }

/-- Definition 2 and Proposition 3: the number of runs of `A` on `v` ending in state `q`.
The nullary product is one. Different runs leading to the same state are all counted. -/
def runCount (A : TreeAutomaton C) : Value C → Fin A.stateCount → Nat
  | .node c children, q =>
    (((A.rules _ c).filter (fun tr ↦ tr.2 == q)).map fun tr ↦
      (List.ofFn fun i ↦ A.runCount (children i) (tr.1 i)).foldl (· * ·) 1).sum

/-- Definition 2: the basic function `p_A`, counting accepting runs of `A` on `v`. -/
def basic (A : TreeAutomaton C) (v : Value C) : Nat := A.runCount v A.final

end TreeAutomaton

/-- Remove duplicate elements from a finite list while preserving membership. -/
noncomputable def dedupFinite {α : Type u} (xs : List α) :
    {ys : List α // ys.Nodup ∧ ∀ x, x ∈ ys ↔ x ∈ xs} := by
  classical
  induction xs with
  | nil => exact ⟨[], by simp⟩
  | cons x xs ih =>
    obtain ⟨ys, hy, heq⟩ := ih
    by_cases hx : x ∈ ys
    · refine ⟨ys, hy, ?_⟩
      intro a
      simp only [List.mem_cons, ← heq]
      exact ⟨fun ha => Or.inr ha, fun h => h.elim (fun h => h ▸ hx) id⟩
    · refine ⟨x :: ys, List.nodup_cons.mpr ⟨hx, hy⟩, ?_⟩
      intro a
      simp only [List.mem_cons, heq]

/-- Encode a pair of states `(i, j)` into `Fin (a * b + 1)`, reserving the last state
`Fin.last (a * b)` as a padding state. -/
def productState {a b : Nat} (i : Fin a) (j : Fin b) : Fin (a * b + 1) :=
  ⟨i.val * b + j.val, by
    have h : i.val * b + j.val < (i.val + 1) * b := by
      simp only [Nat.add_mul, Nat.one_mul]
      exact Nat.add_lt_add_left j.isLt _
    have h' : (i.val + 1) * b ≤ a * b := Nat.mul_le_mul_right b (Nat.succ_le_of_lt i.isLt)
    exact Nat.lt_trans (Nat.lt_of_lt_of_le h h') (Nat.lt_succ_self _)⟩

/-- Pair encoding is injective; the last finite state is reserved for padding. -/
theorem productState_injective {a b : Nat} (i i' : Fin a) (j j' : Fin b)
    (h : productState i j = productState i' j') : i = i' ∧ j = j' := by
  have hb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have quot (x : Fin a) (y : Fin b) : (x.val * b + y.val) / b = x.val := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt y.isLt]
    simp
  have rem (x : Fin a) (y : Fin b) : (x.val * b + y.val) % b = y.val := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt y.isLt]
  have heq : i.val * b + j.val = i'.val * b + j'.val := congrArg Fin.val h
  constructor
  · apply Fin.ext
    have hd := congrArg (fun n : Nat ↦ n / b) heq
    simpa only [quot] using hd
  · apply Fin.ext
    have hm := congrArg (fun n : Nat ↦ n % b) heq
    simpa only [rem] using hm

/-- Encoded pairs cannot equal the fresh padding state. -/
theorem productState_ne_padding {a b : Nat} (i : Fin a) (j : Fin b) :
    productState i j ≠ Fin.last (a * b) := by
  have h : i.val * b + j.val < a * b := by
    have h₁ : i.val * b + j.val < (i.val + 1) * b := by
      simp only [Nat.add_mul, Nat.one_mul]
      exact Nat.add_lt_add_left j.isLt _
    exact Nat.lt_of_lt_of_le h₁ (Nat.mul_le_mul_right b (Nat.succ_le_of_lt i.isLt))
  intro heq
  have hv : i.val * b + j.val = a * b := congrArg Fin.val heq
  omega

namespace TreeAutomaton

variable {C : Nat → Type u}

/-- Raw transitions of the Cartesian-product automaton, together with one self-loop on
the padding state `Fin.last (A.stateCount * B.stateCount)` for each constructor. -/
def productRules (A B : TreeAutomaton C) (n : Nat) (c : C n) :
    List ((Fin n → Fin (A.stateCount * B.stateCount + 1)) ×
      Fin (A.stateCount * B.stateCount + 1)) :=
  ((A.rules n c).flatMap fun ar ↦ (B.rules n c).map fun br ↦
    (fun i ↦ productState (ar.1 i) (br.1 i), productState ar.2 br.2)) ++
    [(fun _ ↦ Fin.last _, Fin.last _)]

/-- Cartesian-product automaton construction used in Lemmas 7 and 9. Pair states encode
the product `Fin A.stateCount × Fin B.stateCount`, and the final state is
`productState A.final B.final`. A separate unreachable padding state has a transition for
each constructor so that `has_rule` holds even when `A` and `B` have disjoint rule supports. -/
noncomputable def product (S : FiniteConstructors C) (A B : TreeAutomaton C) :
    TreeAutomaton C where
  stateCount := A.stateCount * B.stateCount + 1
  final := productState A.final B.final
  rules := fun n c ↦ (dedupFinite (productRules A B n c)).1
  no_duplicate_rules := fun n c ↦ (dedupFinite (productRules A B n c)).2.1
  finite_rules := by
    refine ⟨S.symbols, ?_⟩
    intro n c _
    exact S.contains n c
  has_rule := by
    obtain ⟨n, ⟨c⟩⟩ := S.nonempty
    refine ⟨n, c, ?_⟩
    apply List.length_pos_iff.mpr
    let pad : (Fin n → Fin (A.stateCount * B.stateCount + 1)) ×
        Fin (A.stateCount * B.stateCount + 1) := (fun _ ↦ Fin.last _, Fin.last _)
    have hpad : pad ∈ (dedupFinite (productRules A B n c)).1 :=
      ((dedupFinite (productRules A B n c)).2.2 pad).2 (by simp [productRules, pad])
    exact List.ne_nil_of_mem hpad

/-- Product transitions are precisely the paired transitions together with the padding
transition. -/
theorem product_rule_mem_iff (S : FiniteConstructors C) (A B : TreeAutomaton C)
    (n : Nat) (c : C n) (tr : (Fin n → Fin (A.stateCount * B.stateCount + 1)) ×
      Fin (A.stateCount * B.stateCount + 1)) :
    tr ∈ (product S A B).rules n c ↔ tr ∈ productRules A B n c :=
  (dedupFinite (productRules A B n c)).2.2 tr

end TreeAutomaton

/-- Definition 2: a function `Value C → Nat` is a basic resource function (`f ∈ BF`) if it
is the accepting-run count `A.basic` of some tree automaton `A` over `C`. -/
def IsBasicFunction (C : Nat → Type u) (f : Value C → Nat) : Prop :=
  ∃ A : TreeAutomaton C, A.basic = f

/-- The type `BF` of basic resource functions over `C` (Definition 2, p. 245). Two elements
of `BasicFunction C` are equal if and only if they assign the same run count to every value. -/
abbrev BasicFunction (C : Nat → Type u) := {f : Value C → Nat // IsBasicFunction C f}

/-- A fixed choice of one representative automaton per basic function, modeling the paper's
chosen enumeration `𝔄` (§3, p. 246). -/
structure RepPolicy (C : Nat → Type u) where
  rep : BasicFunction C → TreeAutomaton C
  rep_basic : ∀ p, (rep p).basic = p.val

/-- Classical representative policy choosing one witness automaton for each basic function. -/
noncomputable def classicalRepPolicy (C : Nat → Type u) : RepPolicy C where
  rep p := Classical.choose p.property
  rep_basic p := Classical.choose_spec p.property

namespace BasicFunction

variable {C : Nat → Type u}

/-- Project a tree automaton `A` to the basic resource function `p_A` it computes. -/
def ofAutomaton (A : TreeAutomaton C) : BasicFunction C :=
  ⟨A.basic, ⟨A, rfl⟩⟩

/-- The canonical basic resource function `p_∅` (Definition 2, p. 245). -/
def canonical (S : FiniteConstructors C) : BasicFunction C :=
  ofAutomaton (TreeAutomaton.canonical S)

/-- The basic resource function `p_{(A, q)}` of `A` rerooted at state `q` (§3, p. 245). -/
def reroot (A : TreeAutomaton C) (q : Fin A.stateCount) : BasicFunction C :=
  ofAutomaton (A.reroot q)

/-- Product of two basic functions via the Cartesian-product automaton of their chosen
representatives (Lemmas 7 and 9, pp. 247–248). -/
noncomputable def product (S : FiniteConstructors C) (P : RepPolicy C)
    (p₁ p₂ : BasicFunction C) : BasicFunction C :=
  ofAutomaton (TreeAutomaton.product S (P.rep p₁) (P.rep p₂))

end BasicFunction

/-- A resource annotation of length `n` (§3, p. 248): a finite list of weighted tuples of
basic resource functions. Duplicate tuples contribute additively to the represented
finitely supported coefficient family. Coefficients are nonnegative rationals. -/
abbrev Annotation (C : Nat → Type u) (n : Nat) :=
  List ((Fin n → BasicFunction C) × {q : Rat // 0 ≤ q})

/-- The all-canonical tuple `∅⃗ = (∅, …, ∅)` of length `n` (§3, p. 248). -/
def canonicalTuple {C : Nat → Type u} (S : FiniteConstructors C) (n : Nat) :
    Fin n → BasicFunction C := fun _ ↦ BasicFunction.canonical S

/-- Constant addition `Q + K` (§3, p. 249): add `K` to the coefficient of the canonical
tuple `∅⃗`, retaining all existing entries. -/
def addConstant {C : Nat → Type u} {n : Nat} (S : FiniteConstructors C)
    (Q : Annotation C n) (K : {q : Rat // 0 ≤ q}) : Annotation C n :=
  (canonicalTuple S n, K) :: Q

/-- Projection `π_l^{B₁,…,B_m}(Q)` of a length `l + m` annotation at a fixed suffix tuple
of basic functions (§3, p. 249). -/
noncomputable def annotationProject {C : Nat → Type u} {l m : Nat}
    (Q : Annotation C (l + m)) (suffix : Fin m → BasicFunction C) : Annotation C l := by
  classical
  exact Q.filterMap fun entry ↦
    if (fun i ↦ entry.1 (Fin.natAdd l i)) = suffix then
      some (fun i ↦ entry.1 (Fin.castAdd m i), entry.2)
    else none

/-- Definition 8: the multivariate basic function `p_{(A₁,…,A_n)}(v₁,…,v_n) =
p_{A₁}(v₁) ⋯ p_{A_n}(v_n)` evaluated on a sequence of values. -/
def multivariateBasic {C : Nat → Type u} {n : Nat}
    (ps : Fin n → BasicFunction C) (values : Fin n → Value C) : Nat :=
  (List.ofFn fun i ↦ (ps i).val (values i)).foldl (· * ·) 1

/-- Definitions 5 and 10: the potential `Φ(v₁, …, v_n : Q)` of a sequence of constructor
values with respect to an annotation `Q`. -/
def potential {C : Nat → Type u} {n : Nat}
    (Q : Annotation C n) (values : Fin n → Value C) : Rat :=
  (Q.map fun entry ↦ entry.2.1 * (multivariateBasic entry.1 values : Rat)).sum

/-- Definition 5: a function `r : Value C → Rat` is a resource function (`r ∈ RF`) if it is
a nonnegative rational linear combination of basic functions, i.e., the potential of a
length-1 annotation. -/
def IsResourceFunction (C : Nat → Type u) (r : Value C → Rat) : Prop :=
  ∃ Q : Annotation C 1, ∀ v, r v = potential Q (fun _ ↦ v)

/-- Child basic-function tuples generated by expanding the last coordinate of `tuple` at
constructor `c` using the transitions of its fixed representative `P.rep (tuple (Fin.last m))`
and rerooting at each child state. -/
def shiftTuples {C : Nat → Type u} {m n : Nat} (P : RepPolicy C) (c : C n)
    (tuple : Fin (m + 1) → BasicFunction C) : List (Fin (m + n) → BasicFunction C) :=
  let A := P.rep (tuple (Fin.last m))
  (((A.rules n c).filter fun tr ↦ tr.2 == A.final)).map fun tr ↦
    Fin.addCases (fun i ↦ tuple (Fin.castSucc i)) (fun i ↦ BasicFunction.reroot A (tr.1 i))

/-- Definition 11: the additive shift `◁_c(Q)` of a length `m + 1` annotation at an `n`-ary
constructor `c`. For each entry, the last basic function `p` is expanded along the transitions
into the final state of its fixed representative `P.rep p`, replacing `p` with the rerooted
child basic functions. -/
def additiveShift {C : Nat → Type u} {m n : Nat}
    (P : RepPolicy C) (c : C n) (Q : Annotation C (m + 1)) : Annotation C (m + n) :=
  Q.flatMap fun entry ↦ (shiftTuples P c entry.1).map fun outTuple ↦ (outTuple, entry.2)

/-- Lemma 13: the sharing operator `Υ(Q)` replacing the last two basic functions of each
tuple in a length `m + 2` annotation by their product basic function. -/
noncomputable def annotationShare {C : Nat → Type u} {m : Nat}
    (S : FiniteConstructors C) (P : RepPolicy C) (Q : Annotation C (m + 2)) :
    Annotation C (m + 1) :=
  Q.map fun entry ↦
    (Fin.addCases (fun i ↦ entry.1 (Fin.castAdd 2 i))
      (fun _ ↦ BasicFunction.product S P
        (entry.1 (Fin.natAdd m (0 : Fin 2)))
        (entry.1 (Fin.natAdd m (1 : Fin 2)))), entry.2)

end HofmannMoser


