-- Prove2me | solution 2 for KitchenQuery.tasteCost_le_cert_mul
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:38:49.068273+00:00
-- url     : https://prove2.me/submissions/7a4d5b1c-f138-46e6-b307-713125c58944

import Mathlib
import Definitions.Def_Novelty_KitchenCertificateSquare
import Definitions.Def_Novelty_KitchenQueryComplexity

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Novelty/KitchenQueryComplexity.lean ====
/-!
# Kitchen query complexity: cooking, tasting, and an unconditional `P ≠ NP` in the kitchen

The slogan "a recipe is an algorithm, so `C(R)` versus `V(R)` is `P` versus `NP`" is
usually left as a metaphor.  This file makes the metaphor into a theorem by choosing a
computational model in which the separation is *provable*: the deterministic
**decision-tree (query) model**.

* A *pantry* of `n` ingredients is a Boolean vector `x : Fin n → Bool` (each ingredient is
  fresh/spoiled, whipped/flat, ...).
* A *dish* is a predicate `f : Pantry n → Bool`: is the result good?
* *Cooking* means touching all `n` ingredients: `C(R) = n`.
* *Tasting* is modelled by a `Taste` tree: adaptively probe individual ingredients of the
  finished dish and then declare it good or bad.  `V(R)` is the minimal depth of a taste
  tree computing `f` (`tasteCost`).
* *Nondeterministic verification* (a "garnish" pointing at what to taste) is certificate
  complexity: a set `S` of probes with `IsCertificate f x S`.

The main results are:

* `Taste.card_path_le_depth`, `Taste.eval_eq_of_agree`: the path lemma, the technical
  heart of every lower bound below.
* `sensitivity_le_tasteCost`: sensitivity is a lower bound on tasting time.
* `tasteCost_le_card_ingredients`: tasting is never slower than cooking, `V(R) ≤ C(R)`.
* `tasteCost_allFresh`: the "everything must be fresh" dish is *evasive*: `V = C = n`.
* `kitchen_P_ne_NP`: the anySpoiled dish has a one-probe nondeterministic certificate at
  every bad pantry, yet every deterministic taster needs all `n` probes.  This is an
  unconditional separation of deterministic and nondeterministic kitchen verification.
* `souffle_no_certificate_shortcut`: for the soufflé dish (parity of the pantry) *even*
  nondeterministic verification is useless — every certificate at every pantry is the whole
  pantry.  This is the honest version of "soufflé verification is co-NP-hard": the soufflé
  is hard to verify from *both* sides, unlike the salad.
* `tasteCost_zero_iff_constant`: you cannot tell whether the soufflé rose without cutting
  into it.

No claim about Navier–Stokes or `PSPACE` is made: those need a physical model that timing
data does not supply.  What *is* proved is the exact combinatorial shadow of the
conjecture.
-/

namespace KitchenQuery

open Finset

-- [dropped: platform already declares Pantry]
-- [dropped: platform already declares Dish]
-- [dropped: platform already declares Taste]
namespace Taste

variable {n : ℕ}

-- [dropped: platform already declares depth]
-- [dropped: platform already declares eval]
-- [dropped: platform already declares path]
@[simp] lemma depth_serve (b : Bool) : (serve b : Taste n).depth = 0 := rfl
@[simp] lemma eval_serve (b : Bool) (x : Pantry n) : (serve b : Taste n).eval x = b := rfl
@[simp] lemma path_serve (b : Bool) (x : Pantry n) : (serve b : Taste n).path x = ∅ := rfl

/-- **Path lemma, part 1.** A tasting strategy probes at most `depth` ingredients. -/
theorem card_path_le_depth (t : Taste n) (x : Pantry n) : (t.path x).card ≤ t.depth := by
  induction t with
  | serve b => simp
  | probe i l r hl hr =>
      have h : ((if x i then r.path x else l.path x)).card ≤ max l.depth r.depth := by
        by_cases hx : x i
        · simp only [hx, if_true]
          exact le_trans (hr) (le_max_right _ _)
        · simp only [hx, if_false, Bool.false_eq_true]
          exact le_trans (hl) (le_max_left _ _)
      refine le_trans (Finset.card_insert_le _ _) ?_
      simp only [depth]
      omega

/-- **Path lemma, part 2.** The verdict only depends on the ingredients actually probed. -/
theorem eval_eq_of_agree (t : Taste n) (x y : Pantry n)
    (h : ∀ i ∈ t.path x, y i = x i) : t.eval y = t.eval x := by
  induction t with
  | serve b => rfl
  | probe i l r hl hr =>
      have hi : y i = x i := h i (by simp [path])
      by_cases hx : x i
      · have hy : y i = true := by rw [hi]; exact hx
        simp only [eval, hy, hx, if_true]
        exact hr (fun j hj => h j (by simp [path, hx, hj]))
      · have hy : y i = false := by rw [hi]; simpa using hx
        simp only [eval, hy, hx, if_false, Bool.false_eq_true]
        exact hl (fun j hj => h j (by simp [path, hx, hj]))

end Taste

variable {n : ℕ}

-- [dropped: platform already declares Computes]
-- [dropped: platform already declares brute]
lemma brute_depth_le (f : Dish n) (k : ℕ) (a : Pantry n) : (brute f k a).depth ≤ k := by
  induction k generalizing a with
  | zero => simp [brute]
  | succ k ih =>
      by_cases h : k < n
      · simp only [brute, h, dif_pos, Taste.depth]
        have := ih (Function.update a ⟨k, h⟩ false)
        have := ih (Function.update a ⟨k, h⟩ true)
        omega
      · simp only [brute, h, dif_neg, not_false_iff]
        exact le_trans (ih a) (Nat.le_succ k)

/-- The exhaustive taster reconstructs the pantry on the coordinates it probes. -/
theorem brute_eval (f : Dish n) (k : ℕ) (a x : Pantry n) :
    (brute f k a).eval x = f (fun j => if (j : ℕ) < k then x j else a j) := by
  induction k generalizing a with
  | zero => simp [brute]
  | succ k ih =>
      by_cases h : k < n
      · have key : ∀ b : Bool, x ⟨k, h⟩ = b →
            (brute f k (Function.update a ⟨k, h⟩ b)).eval x =
              f (fun j => if (j : ℕ) < k + 1 then x j else a j) := by
          intro b hb
          rw [ih]
          congr 1
          funext j
          by_cases h1 : (j : ℕ) < k
          · simp [h1, Nat.lt_succ_of_lt h1]
          · by_cases h2 : (j : ℕ) = k
            · have hj : j = ⟨k, h⟩ := by ext; simpa using h2
              subst hj
              simp [hb]
            · have : ¬ (j : ℕ) < k + 1 := by omega
              have hne : j ≠ ⟨k, h⟩ := by
                intro hc; exact h2 (by rw [hc])
              simp [h1, this, Function.update_of_ne hne]
        by_cases hx : x ⟨k, h⟩
        · simp only [brute, h, dif_pos, Taste.eval, hx, if_true]
          exact key true hx
        · have hx' : x ⟨k, h⟩ = false := by simpa using hx
          simp only [brute, h, dif_pos, Taste.eval, hx', if_false, Bool.false_eq_true]
          exact key false hx'
      · simp only [brute, h, dif_neg, not_false_iff]
        rw [ih]
        congr 1
        funext j
        have hj : (j : ℕ) < k := by omega
        simp [hj, Nat.lt_succ_of_lt hj]

theorem brute_computes (f : Dish n) (a : Pantry n) : Computes (brute f n a) f := by
  intro x
  rw [brute_eval]
  congr 1
  funext j
  simp [j.isLt]

/-! ### Verification cost -/

/-- The set of achievable tasting depths for a dish. -/
-- [dropped: platform already declares tasteDepths]
lemma tasteDepths_nonempty (f : Dish n) : (tasteDepths f).Nonempty :=
  ⟨n, brute f n (fun _ => false), brute_computes f _, brute_depth_le f n _⟩

/-- **Verification time `V(R)`**: the least number of probes of a worst-case-optimal
adaptive taster. -/
-- [dropped: platform already declares tasteCost]
-- [dropped: platform already declares cookCost]
lemma tasteCost_mem (f : Dish n) : tasteCost f ∈ tasteDepths f :=
  Nat.sInf_mem (tasteDepths_nonempty f)

lemma tasteCost_le_of_computes {t : Taste n} {f : Dish n} (h : Computes t f) :
    tasteCost f ≤ t.depth :=
  Nat.sInf_le ⟨t, h, le_rfl⟩

/-- **`V(R) ≤ C(R)`: tasting never costs more than cooking.** -/
theorem tasteCost_le_card_ingredients (f : Dish n) : tasteCost f ≤ cookCost f :=
  Nat.sInf_le ⟨brute f n (fun _ => false), brute_computes f _, brute_depth_le f n _⟩

/-- There is an optimal taster realising `tasteCost`. -/
lemma exists_optimal_taste (f : Dish n) :
    ∃ t : Taste n, Computes t f ∧ t.depth ≤ tasteCost f := tasteCost_mem f

/-! ### Sensitivity: the universal lower bound on tasting -/

/-- Ingredient `i` is *pivotal* for the dish `f` at the pantry `x` if swapping it alone
changes the verdict. -/
-- [dropped: platform already declares Pivotal]
-- [dropped: platform already declares pivotalSet]
theorem pivotal_mem_path {t : Taste n} {f : Dish n} (ht : Computes t f) (x : Pantry n)
    {i : Fin n} (hi : Pivotal f x i) : i ∈ t.path x := by
  by_contra hmem
  set y := Function.update x i (!x i) with hy
  have hagree : ∀ j ∈ t.path x, y j = x j := by
    intro j hj
    have hne : j ≠ i := by rintro rfl; exact hmem hj
    simp [hy, Function.update_of_ne hne]
  have : f y = f x := by
    rw [← ht y, ← ht x]
    exact t.eval_eq_of_agree x y hagree
  exact hi this

/-- **Sensitivity lower bound.** No taster can beat the number of pivotal ingredients. -/
theorem pivotalSet_card_le_tasteCost (f : Dish n) (x : Pantry n) :
    (pivotalSet f x).card ≤ tasteCost f := by
  obtain ⟨t, ht, hd⟩ := exists_optimal_taste f
  refine le_trans (le_trans (Finset.card_le_card ?_) (t.card_path_le_depth x)) hd
  intro i hi
  exact pivotal_mem_path ht x (by simpa [pivotalSet] using hi)

/-- The maximal sensitivity of a dish is a lower bound for verification time. -/
theorem sensitivity_le_tasteCost (f : Dish n) (x : Pantry n) (m : ℕ)
    (hm : m ≤ (pivotalSet f x).card) : m ≤ tasteCost f :=
  le_trans hm (pivotalSet_card_le_tasteCost f x)

/-! ### Nondeterministic verification: certificates -/

/-- A *garnish certificate*: probing the ingredients in `S` already pins the verdict. -/
-- [dropped: platform already declares IsCertificate]
theorem certificate_of_computes {t : Taste n} {f : Dish n} (ht : Computes t f) (x : Pantry n) :
    IsCertificate f x (t.path x) ∧ (t.path x).card ≤ t.depth := by
  refine ⟨fun y hy => ?_, t.card_path_le_depth x⟩
  rw [← ht y, ← ht x]
  exact t.eval_eq_of_agree x y hy

/-- **Nondeterminism is at least as fast as determinism in the kitchen.** -/
theorem exists_certificate_card_le_tasteCost (f : Dish n) (x : Pantry n) :
    ∃ S : Finset (Fin n), IsCertificate f x S ∧ S.card ≤ tasteCost f := by
  obtain ⟨t, ht, hd⟩ := exists_optimal_taste f
  exact ⟨t.path x, (certificate_of_computes ht x).1,
    le_trans ((certificate_of_computes ht x).2) hd⟩

/-- Certificates must mention every pivotal ingredient. -/
theorem pivotal_mem_certificate {f : Dish n} {x : Pantry n} {S : Finset (Fin n)}
    (hS : IsCertificate f x S) {i : Fin n} (hi : Pivotal f x i) : i ∈ S := by
  by_contra hmem
  refine hi (hS _ ?_)
  intro j hj
  have hne : j ≠ i := by rintro rfl; exact hmem hj
  simp [Function.update_of_ne hne]

theorem pivotalSet_subset_certificate {f : Dish n} {x : Pantry n} {S : Finset (Fin n)}
    (hS : IsCertificate f x S) : pivotalSet f x ⊆ S := by
  intro i hi
  exact pivotal_mem_certificate hS (by simpa [pivotalSet] using hi)

/-! ### Three model dishes -/

/-- **Salad / constant dish**: no probing needed. -/
theorem tasteCost_const (b : Bool) : tasteCost (fun _ : Pantry n => b) = 0 :=
  Nat.le_antisymm (Nat.sInf_le ⟨.serve b, fun _ => rfl, le_rfl⟩) (Nat.zero_le _)

/-- **You cannot judge a dish without tasting it**: a zero-probe verdict is possible exactly
for dishes whose quality is decided in advance. -/
theorem tasteCost_zero_iff_constant (f : Dish n) :
    tasteCost f = 0 ↔ ∃ b, ∀ x, f x = b := by
  constructor
  · intro h
    obtain ⟨t, ht, hd⟩ := exists_optimal_taste f
    rw [h] at hd
    cases t with
    | serve b => exact ⟨b, fun x => (ht x).symm ▸ rfl⟩
    | probe i l r => simp [Taste.depth] at hd
  · rintro ⟨b, hb⟩
    have : (fun x : Pantry n => f x) = fun _ => b := funext hb
    simpa [this] using tasteCost_const (n := n) b

/-- **The one-ingredient salad**: good iff the single flagged ingredient is fresh. -/
-- [dropped: platform already declares salad]
theorem tasteCost_salad (i : Fin n) : tasteCost (salad i) = 1 := by
  refine Nat.le_antisymm (Nat.sInf_le ⟨.probe i (.serve false) (.serve true), ?_, by simp [Taste.depth]⟩) ?_
  · intro x
    by_cases hx : x i <;> simp [Taste.eval, salad, hx]
  · rcases Nat.eq_zero_or_pos (tasteCost (salad i)) with h | h
    · obtain ⟨b, hb⟩ := (tasteCost_zero_iff_constant _).1 h
      have h1 : (true : Bool) = b := hb (fun _ => true)
      have h2 : (false : Bool) = b := hb (fun _ => false)
      exact absurd (h1.trans h2.symm) (by simp)
    · exact h

/-- **`anySpoiled`**: the dish is bad as soon as one ingredient is spoiled.  (Written as an
OR over the pantry.) -/
-- [dropped: platform already declares anySpoiled]
theorem anySpoiled_certificate {x : Pantry n} {i : Fin n} (hi : x i = true) :
    IsCertificate anySpoiled x {i} := by
  intro y hy
  have hyi : y i = true := by rw [hy i (by simp), hi]
  simp only [anySpoiled, decide_eq_decide]
  exact ⟨fun _ => ⟨i, hi⟩, fun _ => ⟨i, hyi⟩⟩

/-- At the all-fresh pantry every ingredient is pivotal for `anySpoiled`. -/
theorem anySpoiled_pivotalSet_univ :
    pivotalSet (anySpoiled (n := n)) (fun _ => false) = Finset.univ := by
  ext i
  simp only [pivotalSet, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  intro hc
  have h1 : anySpoiled (Function.update (fun _ : Fin n => false) i (!false)) = true := by
    simp only [anySpoiled, decide_eq_true_eq]
    exact ⟨i, by simp⟩
  have h2 : anySpoiled (fun _ : Fin n => false) = false := by
    simp [anySpoiled]
  rw [h1, h2] at hc
  exact Bool.noConfusion hc

/-- **Determinstic verification of `anySpoiled` costs a full cook.** -/
theorem tasteCost_anySpoiled : tasteCost (anySpoiled (n := n)) = n := by
  refine Nat.le_antisymm (tasteCost_le_card_ingredients _) ?_
  have := pivotalSet_card_le_tasteCost (anySpoiled (n := n)) (fun _ => false)
  rwa [anySpoiled_pivotalSet_univ, Finset.card_univ, Fintype.card_fin] at this

/-- **`P ≠ NP` in the kitchen (unconditional, in the query model).**
For `n ≥ 2` the dish `anySpoiled` has, at every bad pantry, a *one-probe* nondeterministic
certificate, while every deterministic taster must probe all `n` ingredients: verification
with a hint is strictly and unboundedly faster than verification without one. -/
theorem kitchen_P_ne_NP (hn : 2 ≤ n) :
    (∀ x : Pantry n, (∃ i, x i = true) →
      ∃ S : Finset (Fin n), IsCertificate anySpoiled x S ∧ S.card = 1) ∧
    tasteCost (anySpoiled (n := n)) = n ∧ 1 < tasteCost (anySpoiled (n := n)) := by
  refine ⟨?_, tasteCost_anySpoiled, ?_⟩
  · rintro x ⟨i, hi⟩
    exact ⟨{i}, anySpoiled_certificate hi, Finset.card_singleton i⟩
  · rw [tasteCost_anySpoiled]; omega

/-! ### The soufflé: parity, hard from both sides -/

/-- The soufflé verdict: it rises exactly when an odd number of the `n` critical steps were
performed correctly — a parity, the canonical "no partial information" dish. -/
-- [dropped: platform already declares souffle]
lemma souffle_update (x : Pantry n) (i : Fin n) :
    souffle (Function.update x i (!x i)) ≠ souffle x := by
  classical
  have hmem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hx : (∑ j, if x j then 1 else 0)
      = (if x i then 1 else 0) + ∑ j ∈ Finset.univ.erase i, if x j then 1 else 0 := by
    rw [← Finset.add_sum_erase _ _ hmem]
  have hu : (∑ j, if Function.update x i (!x i) j then 1 else 0)
      = (if !x i then 1 else 0) + ∑ j ∈ Finset.univ.erase i, if x j then 1 else 0 := by
    rw [← Finset.add_sum_erase _ _ hmem]
    simp only [Function.update_self]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Function.update_of_ne hne]
  simp only [souffle, ne_eq, decide_eq_decide, Nat.odd_iff, hx, hu]
  cases hxi : x i <;> simp <;> omega

/-- Every ingredient is pivotal for the soufflé, at *every* pantry. -/
theorem souffle_pivotalSet_univ (x : Pantry n) :
    pivotalSet (souffle (n := n)) x = Finset.univ := by
  ext i
  simp only [pivotalSet, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact souffle_update x i

/-- **The soufflé is evasive: `V(R) = C(R) = n`.** -/
theorem tasteCost_souffle : tasteCost (souffle (n := n)) = n := by
  refine Nat.le_antisymm (tasteCost_le_card_ingredients _) ?_
  have := pivotalSet_card_le_tasteCost (souffle (n := n)) (fun _ => false)
  rwa [souffle_pivotalSet_univ, Finset.card_univ, Fintype.card_fin] at this

/-- **Soufflé theorem: no nondeterministic shortcut, at either verdict.**
Unlike the salad, no garnish helps: every certificate at every pantry is the entire pantry,
so nondeterministic *and* co-nondeterministic verification both cost a full cook. -/
theorem souffle_no_certificate_shortcut (x : Pantry n) (S : Finset (Fin n))
    (hS : IsCertificate (souffle (n := n)) x S) : S = Finset.univ := by
  refine Finset.eq_univ_of_card S ?_
  have hsub : pivotalSet (souffle (n := n)) x ⊆ S := pivotalSet_subset_certificate hS
  have := Finset.card_le_card hsub
  rw [souffle_pivotalSet_univ, Finset.card_univ, Fintype.card_fin] at this
  have hub : S.card ≤ n := by simpa using Finset.card_le_univ S
  rw [Fintype.card_fin]
  omega

/-- The soufflé strictly separates from the salad: for `n ≥ 2`, tasting the soufflé costs
strictly more than tasting a salad, and exactly as much as cooking it. -/
theorem souffle_vs_salad (hn : 2 ≤ n) (i : Fin n) :
    tasteCost (salad i) < tasteCost (souffle (n := n)) ∧
      tasteCost (souffle (n := n)) = cookCost (souffle (n := n)) := by
  rw [tasteCost_salad, tasteCost_souffle]
  exact ⟨by omega, rfl⟩

end KitchenQuery
-- ==== upstream: Packages/Catalog/Novelty/KitchenCertificateSquare.lean ====
/-!
# `P = NP ∩ co-NP`, up to squaring, in the kitchen

Third research cycle on the query model of `Novelty.KitchenQueryComplexity`.

Cycle 1 separated deterministic from nondeterministic verification (`kitchen_P_ne_NP`) and
showed the soufflé has no nondeterministic shortcut at either verdict.  That raises the sharp
question: *if a dish has short goodness proofs and short badness proofs, must it be quick to
taste outright?*  The answer proved here is yes, up to a product:

> **Main theorem** (`tasteCost_le_cert_mul`).  If every good pantry has a goodness
> certificate of at most `m` probes and every bad pantry has a badness certificate of at most
> `k` probes, then there is a deterministic adaptive taster using at most `k * m` probes.

Equivalently `D(f) ≤ C₀(f) · C₁(f)`: in the kitchen, `NP ∩ co-NP` collapses into `P` at the
cost of squaring the tasting time.  This is exactly the boundary that the soufflé escapes:
`souffle_no_certificate_shortcut` shows both of its certificate complexities are `n`, so the
theorem only yields the vacuous bound `n²`, whereas for `anySpoiled` the bound `1 · n = n` is
attained exactly (`anySpoiled_bound_tight`).

The proof is the classical adaptive covering argument, formalised in three pieces:

* `cert_inter_nonempty`: a goodness certificate and a badness certificate always overlap —
  the combinatorial heart.
* `restrictDish`, `restrict_isCertificate`: fixing the ingredients of a certificate shrinks
  every opposite certificate by at least one probe.
* `queryList`: the tasting strategy that probes a whole checklist and then continues
  adaptively, with its depth and evaluation laws.
-/

namespace KitchenQuery

open Finset

variable {n : ℕ}

/-! ### Probing a whole checklist, then continuing -/

-- [dropped: platform already declares queryList]
lemma queryList_depth (L : List (Fin n)) (cont : Pantry n → Taste n) {d : ℕ}
    (hcont : ∀ a, (cont a).depth ≤ d) (a : Pantry n) :
    (queryList L cont a).depth ≤ L.length + d := by
  induction L generalizing a with
  | nil => simpa [queryList] using hcont a
  | cons i L ih =>
      have h1 := ih (Function.update a i false)
      have h2 := ih (Function.update a i true)
      simp only [queryList, Taste.depth, List.length_cons]
      omega

lemma queryList_eval (L : List (Fin n)) (cont : Pantry n → Taste n) (a x : Pantry n) :
    (queryList L cont a).eval x
      = (cont (fun j => if j ∈ L then x j else a j)).eval x := by
  classical
  induction L generalizing a with
  | nil => simp [queryList]
  | cons i L ih =>
      have hkey : ∀ b : Bool, x i = b →
          (queryList L cont (Function.update a i b)).eval x
            = (cont (fun j => if j ∈ i :: L then x j else a j)).eval x := by
        intro b hb
        rw [ih]
        congr 2
        funext j
        by_cases hjL : j ∈ L
        · simp [hjL, List.mem_cons]
        · by_cases hji : j = i
          · subst hji; simp [hjL, hb]
          · simp [hjL, hji, List.mem_cons]
      cases hx : x i
      · simpa [queryList, Taste.eval, hx] using hkey false hx
      · simpa [queryList, Taste.eval, hx] using hkey true hx

/-! ### Certificates overlap -/

/-- **Goodness proofs and badness proofs always overlap.**  If `S` certifies the verdict at
`x` and `T` certifies the opposite verdict at `y`, then `S` and `T` share an ingredient. -/
theorem cert_inter_nonempty {f : Dish n} {x y : Pantry n} {S T : Finset (Fin n)}
    (hS : IsCertificate f x S) (hT : IsCertificate f y T) (hne : f x ≠ f y) :
    (S ∩ T).Nonempty := by
  classical
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  set u : Pantry n := fun j => if j ∈ S then x j else y j with hu
  have h1 : f u = f x := hS u (fun j hj => by simp [hu, hj])
  have h2 : f u = f y := by
    refine hT u (fun j hj => ?_)
    have hjS : j ∉ S := by
      intro hc
      have : j ∈ S ∩ T := Finset.mem_inter.2 ⟨hc, hj⟩
      simp [hemp] at this
    simp [hu, hjS]
  exact hne (h1.symm.trans h2)

/-! ### Restricting a dish along a checklist -/

/-- The dish obtained by fixing the ingredients of `S` to the observed values `a`. -/
-- [dropped: platform already declares restrictDish]
theorem restrict_isCertificate {f : Dish n} {S : Finset (Fin n)} {a z : Pantry n}
    {T : Finset (Fin n)}
    (hT : IsCertificate f (fun j => if j ∈ S then a j else z j) T) :
    IsCertificate (restrictDish f S a) z (T \ S) := by
  classical
  intro y hy
  refine hT (fun j => if j ∈ S then a j else y j) ?_
  intro j hj
  by_cases hjS : j ∈ S
  · simp [hjS]
  · have : j ∈ T \ S := Finset.mem_sdiff.2 ⟨hj, hjS⟩
    simp [hjS, hy j this]

/-! ### The main theorem -/

/-- **`D(f) ≤ C₀(f) · C₁(f)` in the kitchen.**  Short goodness proofs together with short
badness proofs give an outright fast adaptive tasting protocol. -/
theorem tasteCost_le_cert_mul (m : ℕ) : ∀ (k : ℕ) (f : Dish n),
    (∀ x, f x = false → ∃ T : Finset (Fin n), IsCertificate f x T ∧ T.card ≤ k) →
    (∀ x, f x = true → ∃ T : Finset (Fin n), IsCertificate f x T ∧ T.card ≤ m) →
    tasteCost f ≤ k * m := by
  classical
  intro k
  induction k with
  | zero =>
      intro f h0 _
      by_cases hfalse : ∃ x, f x = false
      · obtain ⟨x0, hx0⟩ := hfalse
        obtain ⟨T, hT, hTcard⟩ := h0 x0 hx0
        have hTe : T = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hTcard)
        subst hTe
        have : ∀ y, f y = false := fun y => (hT y (by simp)).trans hx0
        simpa using ((tasteCost_zero_iff_constant f).2 ⟨false, this⟩).le
      · push_neg at hfalse
        have : ∀ y, f y = true := fun y => by
          cases hy : f y
          · exact absurd hy (hfalse y)
          · rfl
        simpa using ((tasteCost_zero_iff_constant f).2 ⟨true, this⟩).le
  | succ k ih =>
      intro f h0 h1
      by_cases htrue : ∃ x, f x = true
      · obtain ⟨x₁, hx₁⟩ := htrue
        obtain ⟨S, hS, hScard⟩ := h1 x₁ hx₁
        -- the restricted dishes still satisfy the hypotheses, with `k` in place of `k+1`
        have hrestr : ∀ a : Pantry n, tasteCost (restrictDish f S a) ≤ k * m := by
          intro a
          refine ih _ ?_ ?_
          · intro z hz
            have hz' : f (fun j => if j ∈ S then a j else z j) = false := hz
            obtain ⟨T, hT, hTcard⟩ := h0 _ hz'
            refine ⟨T \ S, restrict_isCertificate hT, ?_⟩
            obtain ⟨i, hi⟩ := cert_inter_nonempty hS hT (by rw [hx₁, hz']; simp)
            obtain ⟨hiS, hiT⟩ := Finset.mem_inter.1 hi
            have hsub : T \ S ⊆ T.erase i := by
              intro j hj
              obtain ⟨hjT, hjS⟩ := Finset.mem_sdiff.1 hj
              exact Finset.mem_erase.2 ⟨fun hji => hjS (hji ▸ hiS), hjT⟩
            have hcard := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem hiT] at hcard
            have hTpos : 1 ≤ T.card := Finset.card_pos.2 ⟨i, hiT⟩
            omega
          · intro z hz
            have hz' : f (fun j => if j ∈ S then a j else z j) = true := hz
            obtain ⟨T, hT, hTcard⟩ := h1 _ hz'
            exact ⟨T \ S, restrict_isCertificate hT,
              le_trans (Finset.card_le_card (Finset.sdiff_subset)) hTcard⟩
        choose t ht hd using fun a : Pantry n => exists_optimal_taste (restrictDish f S a)
        have hdepth : ∀ a, (t a).depth ≤ k * m := fun a => le_trans (hd a) (hrestr a)
        refine tasteCost_le_of_computes (t := queryList S.toList t (fun _ => false)) ?_ |>.trans ?_
        · intro x
          rw [queryList_eval]
          have := ht (fun j => if j ∈ S.toList then x j else false) x
          rw [this]
          simp only [restrictDish, Finset.mem_toList]
          congr 1
          funext j
          by_cases hj : j ∈ S <;> simp [hj]
        · refine le_trans (queryList_depth _ _ hdepth _) ?_
          rw [Finset.length_toList]
          have : S.card ≤ m := hScard
          calc S.card + k * m ≤ m + k * m := by omega
            _ = (k + 1) * m := by ring
      · push_neg at htrue
        have : ∀ y, f y = false := fun y => by
          cases hy : f y
          · rfl
          · exact absurd hy (htrue y)
        rw [(tasteCost_zero_iff_constant f).2 ⟨false, this⟩]
        exact Nat.zero_le _

/-- **Squaring form.**  If every verdict, good or bad, has a `c`-probe proof, then the dish
can be tasted outright with `c²` probes. -/
theorem tasteCost_le_cert_sq (c : ℕ) (f : Dish n)
    (hc : ∀ x, ∃ T : Finset (Fin n), IsCertificate f x T ∧ T.card ≤ c) :
    tasteCost f ≤ c ^ 2 := by
  have := tasteCost_le_cert_mul (n := n) c c f (fun x _ => hc x) (fun x _ => hc x)
  simpa [pow_two] using this

/-- The bound is attained: for `anySpoiled` the goodness certificates have one probe and the
badness certificate has `n`, and indeed `tasteCost = 1 * n`. -/
theorem anySpoiled_bound_tight :
    tasteCost (anySpoiled (n := n)) = 1 * n := by
  rw [one_mul]
  exact tasteCost_anySpoiled

/-- For the soufflé the theorem is powerless — as it must be, since both certificate
complexities equal `n` and the true cost is `n`, not `n²`.  This exhibits the exact slack of
the product bound. -/
theorem souffle_cert_bound :
    tasteCost (souffle (n := n)) ≤ n ^ 2 ∧ tasteCost (souffle (n := n)) = n := by
  refine ⟨?_, tasteCost_souffle⟩
  refine tasteCost_le_cert_sq n _ (fun x => ⟨Finset.univ, ?_, by simp⟩)
  intro y hy
  have : y = x := funext fun j => hy j (Finset.mem_univ j)
  rw [this]

end KitchenQuery
section
open KitchenQuery
open Finset
variable {n : ℕ}

theorem solution (m : ℕ) :
    ∀ (k : ℕ) (f : Dish n),
    (∀ x, f x = false → ∃ T : Finset (Fin n), IsCertificate f x T ∧ T.card ≤ k) →
    (∀ x, f x = true → ∃ T : Finset (Fin n), IsCertificate f x T ∧ T.card ≤ m) →
    tasteCost f ≤ k * m := by
  first
  | exact KitchenQuery.tasteCost_le_cert_mul m
  | exact KitchenQuery.tasteCost_le_cert_mul
  | exact @KitchenQuery.tasteCost_le_cert_mul m
  | apply KitchenQuery.tasteCost_le_cert_mul
  | exact KitchenQuery.tasteCost_le_cert_mul ..


end
