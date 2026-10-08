-- Prove2me | solution 1 for ProofsInTheBook.Chapter31.chapter31
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:26:15.22363+00:00
-- url     : https://prove2.me/submissions/614dddd6-6c8b-46f2-81b4-3ab83f1d5613

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter31

set_option autoImplicit true


/-!
# Chapter 31: Cayley's formula for the number of trees

From "Proofs from THE BOOK":

**Cayley's formula**: The number of labeled trees on n vertices is n^{n-2}.

The book presents multiple proofs:
1. Prüfer sequences (bijection with [n]^{n-2}).
2. A double counting argument on labeled rooted forests.
3. The determinant formula via Kirchhoff's matrix tree theorem.
-/

namespace ProofsInTheBook.Chapter31

open SimpleGraph

/-!
### Prüfer-code counting side

The Prüfer proof of Cayley's formula builds a bijection between labeled trees
on `n` vertices and words of length `n - 2` over an `n`-letter alphabet.  This
file records the finite counting side of that target code space.
-/













theorem pruferCodeSpace_card (n : ℕ) :
    Fintype.card (pruferCodeSpace n) = n ^ (n - 2) := by
  simp [pruferCodeSpace]















theorem smallestTreeLeaf_adj_neighbor (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) :
    T.1.Adj (smallestTreeLeaf n hn T) (smallestTreeLeafNeighbor n hn T) :=
  (ExistsUnique.exists (unique_adj_smallestTreeLeaf n hn T)).choose_spec

theorem smallestTreeLeaf_neighbor_unique (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n)
    {w : Fin n} (hw : T.1.Adj (smallestTreeLeaf n hn T) w) :
    w = smallestTreeLeafNeighbor n hn T := by
  exact (unique_adj_smallestTreeLeaf n hn T).unique hw
    (smallestTreeLeaf_adj_neighbor n hn T)













theorem treePath_unique (T : LabeledTree n) (u v : Fin n) {p : T.1.Walk u v}
    (hp : p.IsPath) :
    p = treePath T u v := by
  exact (T.2.existsUnique_path u v).unique hp (treePath_isPath T u v)

theorem isTree_path_length_eq_dist (T : LabeledTree n) {u v : Fin n}
    {p : T.1.Walk u v} (hp : p.IsPath) :
    p.length = T.1.dist u v := by
  obtain ⟨q, hqPath, hqLen⟩ := T.2.connected.exists_path_of_dist u v
  have hpq : p = q := (T.2.existsUnique_path u v).unique hp hqPath
  rw [hpq]
  exact hqLen

theorem treePath_length_eq_dist (T : LabeledTree n) (u v : Fin n) :
    (treePath T u v).length = T.1.dist u v :=
  isTree_path_length_eq_dist T (treePath_isPath T u v)

























theorem joyalOffPathValue_adj (X : DoublyRootedLabeledTree n)
    (v : Fin n) (hv : v ∉ joyalPathVertices X) :
    X.1.1.Adj v (joyalOffPathValue X v hv) := by
  let p := treePath X.1 v X.2.1
  have hne : v ≠ X.2.1 := by
    intro h
    subst h
    exact hv (joyal_left_mem_pathVertices X)
  have hp : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  change X.1.1.Adj v p.snd
  exact SimpleGraph.Walk.adj_snd hp





theorem joyalOffPathValue_dist_left_add_one (X : DoublyRootedLabeledTree n)
    (v : Fin n) (hv : v ∉ joyalPathVertices X) :
    X.1.1.dist X.2.1 (joyalOffPathValue X v hv) + 1 = X.1.1.dist X.2.1 v := by
  let p := treePath X.1 v X.2.1
  have hne : v ≠ X.2.1 := by
    intro h
    subst h
    exact hv (joyal_left_mem_pathVertices X)
  have hpNotNil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  have hpPath : p.IsPath := treePath_isPath X.1 v X.2.1
  have htailPath : p.tail.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    have hpNodup : p.support.Nodup := (SimpleGraph.Walk.isPath_def p).mp hpPath
    simpa [p.support_tail_of_not_nil hpNotNil] using hpNodup.tail
  have htailLen : p.tail.length = X.1.1.dist (joyalOffPathValue X v hv) X.2.1 := by
    change p.tail.length = X.1.1.dist p.snd X.2.1
    exact isTree_path_length_eq_dist X.1 htailPath
  have hpLen : p.length = X.1.1.dist v X.2.1 := treePath_length_eq_dist X.1 v X.2.1
  calc
    X.1.1.dist X.2.1 (joyalOffPathValue X v hv) + 1
        = X.1.1.dist (joyalOffPathValue X v hv) X.2.1 + 1 := by
          rw [SimpleGraph.dist_comm]
    _ = p.tail.length + 1 := by rw [htailLen]
    _ = p.length := p.length_tail_add_one hpNotNil
    _ = X.1.1.dist v X.2.1 := hpLen
    _ = X.1.1.dist X.2.1 v := SimpleGraph.dist_comm

theorem joyalOffPathValue_eq_of_adj_dist_left_add_one (X : DoublyRootedLabeledTree n)
    {w z : Fin n} (hw : w ∉ joyalPathVertices X) (hadj : X.1.1.Adj w z)
    (hdist : X.1.1.dist X.2.1 z + 1 = X.1.1.dist X.2.1 w) :
    joyalOffPathValue X w hw = z := by
  classical
  let q := treePath X.1 z X.2.1
  let r : X.1.1.Walk w X.2.1 := SimpleGraph.Walk.cons hadj q
  have hqLen : q.length = X.1.1.dist z X.2.1 := treePath_length_eq_dist X.1 z X.2.1
  have hrLen : r.length = X.1.1.dist w X.2.1 := by
    change q.length + 1 = X.1.1.dist w X.2.1
    rw [hqLen]
    rw [SimpleGraph.dist_comm (u := z) (v := X.2.1)]
    rw [SimpleGraph.dist_comm (u := w) (v := X.2.1)]
    exact hdist
  have hrPath : r.IsPath := SimpleGraph.Walk.isPath_of_length_eq_dist r hrLen
  have hrEq : treePath X.1 w X.2.1 = r := (treePath_unique X.1 w X.2.1 hrPath).symm
  calc
    joyalOffPathValue X w hw = r.snd := by
      change (treePath X.1 w X.2.1).snd = r.snd
      rw [hrEq]
    _ = z := by
      change (SimpleGraph.Walk.cons hadj q).snd = z
      simp





theorem joyalTreeToFunction_apply_of_not_mem (X : DoublyRootedLabeledTree n)
    {v : Fin n} (hv : v ∉ joyalPathVertices X) :
    joyalTreeToFunction X v = joyalOffPathValue X v hv := by
  simp [joyalTreeToFunction, hv]



theorem mem_periodicCore_iff (f : Fin n → Fin n) (v : Fin n) :
    v ∈ periodicCore f ↔ ∃ m : ℕ, 0 < m ∧ f^[m] v = v := by
  simp [periodicCore]





theorem joyalPathTableValue_injective (X : DoublyRootedLabeledTree n)
    {v w : Fin n} (hv : v ∈ joyalPathVertices X) (hw : w ∈ joyalPathVertices X)
    (h : joyalPathTableValue X v hv = joyalPathTableValue X w hw) :
    v = w := by
  classical
  have hvd : v ∈ joyalPathDomainOrder X := by
    simpa [joyalPathDomainOrder] using hv
  have hwd : w ∈ joyalPathDomainOrder X := by
    simpa [joyalPathDomainOrder] using hw
  have hvidx : List.idxOf v (joyalPathDomainOrder X) < (joyalPathRangeOrder X).length := by
    have hdom : List.idxOf v (joyalPathDomainOrder X) < (joyalPathDomainOrder X).length :=
      List.idxOf_lt_length_iff.mpr hvd
    rwa [← joyalPathOrders_length_eq X]
  have hwidx : List.idxOf w (joyalPathDomainOrder X) < (joyalPathRangeOrder X).length := by
    have hdom : List.idxOf w (joyalPathDomainOrder X) < (joyalPathDomainOrder X).length :=
      List.idxOf_lt_length_iff.mpr hwd
    rwa [← joyalPathOrders_length_eq X]
  have hget :
      (joyalPathRangeOrder X)[List.idxOf v (joyalPathDomainOrder X)]'hvidx =
        (joyalPathRangeOrder X)[List.idxOf w (joyalPathDomainOrder X)]'hwidx := by
    simpa [joyalPathTableValue] using h
  have hidx :
      List.idxOf v (joyalPathDomainOrder X) =
        List.idxOf w (joyalPathDomainOrder X) := by
    exact congrArg Fin.val ((joyalPathRangeOrder_nodup X).get_inj_iff.mp hget)
  have hvget :
      (joyalPathDomainOrder X)[List.idxOf v (joyalPathDomainOrder X)]'
        (List.idxOf_lt_length_iff.mpr hvd) = v :=
    List.idxOf_get (List.idxOf_lt_length_iff.mpr hvd)
  have hwget :
      (joyalPathDomainOrder X)[List.idxOf w (joyalPathDomainOrder X)]'
        (List.idxOf_lt_length_iff.mpr hwd) = w :=
    List.idxOf_get (List.idxOf_lt_length_iff.mpr hwd)
  calc
    v = (joyalPathDomainOrder X)[List.idxOf v (joyalPathDomainOrder X)]'
        (List.idxOf_lt_length_iff.mpr hvd) := hvget.symm
    _ = (joyalPathDomainOrder X)[List.idxOf w (joyalPathDomainOrder X)]'
        (List.idxOf_lt_length_iff.mpr hwd) := by simp [hidx]
    _ = w := hwget



theorem joyalPathSelfMap_injective (X : DoublyRootedLabeledTree n) :
    Function.Injective (joyalPathSelfMap X) := by
  intro v w h
  apply Subtype.ext
  apply joyalPathTableValue_injective X v.2 w.2
  have hval := congrArg Subtype.val h
  simpa [joyalPathSelfMap, joyalTreeToFunction_apply_of_mem] using hval

theorem joyalPathSelfMap_iterate_val (X : DoublyRootedLabeledTree n) (m : ℕ)
    (v : {v : Fin n // v ∈ joyalPathVertices X}) :
    ((joyalPathSelfMap X)^[m] v).1 = (joyalTreeToFunction X)^[m] v.1 := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
      simp [Function.iterate_succ, joyalPathSelfMap, ih]

theorem joyalPathVertices_subset_periodicCore (X : DoublyRootedLabeledTree n) :
    joyalPathVertices X ⊆ periodicCore (joyalTreeToFunction X) := by
  classical
  intro v hv
  rw [mem_periodicCore_iff]
  let g := joyalPathSelfMap X
  have hper : (⟨v, hv⟩ : {v : Fin n // v ∈ joyalPathVertices X}) ∈ Function.periodicPts g :=
    (joyalPathSelfMap_injective X).mem_periodicPts _
  rw [Function.mem_periodicPts] at hper
  rcases hper with ⟨m, hmpos, hm⟩
  refine ⟨m, hmpos, ?_⟩
  have hval := congrArg Subtype.val hm
  simpa [g, joyalPathSelfMap_iterate_val] using hval

theorem exists_iterate_mem_joyalPathVertices (X : DoublyRootedLabeledTree n) (v : Fin n) :
    ∃ m : ℕ, (joyalTreeToFunction X)^[m] v ∈ joyalPathVertices X := by
  classical
  let f := joyalTreeToFunction X
  let D := fun v : Fin n => X.1.1.dist X.2.1 v
  have main : ∀ d : ℕ, (∀ e < d, ∀ v : Fin n, D v = e → ∃ m : ℕ, f^[m] v ∈ joyalPathVertices X) →
      ∀ v : Fin n, D v = d → ∃ m : ℕ, f^[m] v ∈ joyalPathVertices X := by
    intro d ih v hvd
    by_cases hv : v ∈ joyalPathVertices X
    · exact ⟨0, by simpa [f] using hv⟩
    · let w := f v
      have hw_eq : w = joyalOffPathValue X v hv := by
        simp [w, f, joyalTreeToFunction_apply_of_not_mem X hv]
      have hdist : D w + 1 = D v := by
        simpa [D, w, hw_eq] using joyalOffPathValue_dist_left_add_one X v hv
      have hwd_lt : D w < d := by omega
      obtain ⟨m, hm⟩ := ih (D w) hwd_lt w rfl
      refine ⟨m + 1, ?_⟩
      simpa [f, Function.iterate_succ, Function.comp_def, w] using hm
  have main' : ∀ d : ℕ, ∀ v : Fin n, D v = d → ∃ m : ℕ, f^[m] v ∈ joyalPathVertices X := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        exact main d (by intro e he; exact ih e he)
  exact main' (D v) v rfl

theorem iterate_joyal_mem_pathVertices_of_mem (X : DoublyRootedLabeledTree n)
    {v : Fin n} (hv : v ∈ joyalPathVertices X) (m : ℕ) :
    (joyalTreeToFunction X)^[m] v ∈ joyalPathVertices X := by
  induction m generalizing v with
  | zero => simpa using hv
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact joyalTreeToFunction_maps_pathVertices X (ih hv)

/--
No vertex off the left-right path is periodic under Joyal's endofunction.
The intended proof uses `joyalOffPathValue_mem_tail_path_to_left`: while outside
the path, iterating strictly shortens the unique path to the left endpoint.
-/
theorem periodicCore_subset_joyalPathVertices (X : DoublyRootedLabeledTree n) :
    periodicCore (joyalTreeToFunction X) ⊆ joyalPathVertices X := by
  classical
  intro v hv
  rw [mem_periodicCore_iff] at hv
  rcases hv with ⟨p, hpPos, hp⟩
  obtain ⟨r, hr⟩ := exists_iterate_mem_joyalPathVertices X v
  let N := (r + 1) * p
  have hrle : r ≤ N := by
    have : r + 1 ≤ N := by
      simpa [N] using Nat.le_mul_of_pos_right (r + 1) hpPos
    omega
  have hNpath : (joyalTreeToFunction X)^[N] v ∈ joyalPathVertices X := by
    have htail := iterate_joyal_mem_pathVertices_of_mem X hr (N - r)
    have hsum : (N - r) + r = N := Nat.sub_add_cancel hrle
    rw [← Function.iterate_add_apply (joyalTreeToFunction X) (N - r) r v] at htail
    simpa [hsum] using htail
  have hperN : (joyalTreeToFunction X)^[N] v = v := by
    have hper : Function.IsPeriodicPt (joyalTreeToFunction X) p v := hp
    have hmul := hper.const_mul (r + 1)
    simpa [Function.IsPeriodicPt, N, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  simpa [hperN] using hNpath

/--
Joyal's path vertices are exactly the periodic core of the associated endofunction.
This is the formal version of the book's subset `M`.
-/
theorem periodicCore_joyalTreeToFunction (X : DoublyRootedLabeledTree n) :
    periodicCore (joyalTreeToFunction X) = joyalPathVertices X := by
  classical
  exact Finset.Subset.antisymm
    (periodicCore_subset_joyalPathVertices X)
    (joyalPathVertices_subset_periodicCore X)

theorem joyalPathVertices_eq_of_function_eq {X Y : DoublyRootedLabeledTree n}
    (hXY : joyalTreeToFunction X = joyalTreeToFunction Y) :
    joyalPathVertices X = joyalPathVertices Y := by
  rw [← periodicCore_joyalTreeToFunction X, ← periodicCore_joyalTreeToFunction Y, hXY]

theorem joyalPathDomainOrder_eq_of_function_eq {X Y : DoublyRootedLabeledTree n}
    (hXY : joyalTreeToFunction X = joyalTreeToFunction Y) :
    joyalPathDomainOrder X = joyalPathDomainOrder Y := by
  simp [joyalPathDomainOrder, joyalPathVertices_eq_of_function_eq hXY]

theorem joyalPathRangeOrder_get_eq_function_domain_get (X : DoublyRootedLabeledTree n)
    (i : ℕ) (hir : i < (joyalPathRangeOrder X).length)
    (hid : i < (joyalPathDomainOrder X).length) :
    (joyalPathRangeOrder X)[i]'hir =
      joyalTreeToFunction X ((joyalPathDomainOrder X)[i]'hid) := by
  classical
  let v := (joyalPathDomainOrder X)[i]'hid
  have hvd : v ∈ joyalPathDomainOrder X := List.get_mem _ _
  have hv : v ∈ joyalPathVertices X := by
    exact (Finset.mem_sort (s := joyalPathVertices X) (r := fun x y : Fin n => x ≤ y)).mp hvd
  rw [joyalTreeToFunction_apply_of_mem X hv]
  unfold joyalPathTableValue
  simp only
  have hidx : List.idxOf v (joyalPathDomainOrder X) = i := by
    simpa [v] using (joyalPathDomainOrder_nodup X).idxOf_getElem i hid
  simp [hidx]

theorem joyalPathRangeOrder_eq_of_function_eq {X Y : DoublyRootedLabeledTree n}
    (hXY : joyalTreeToFunction X = joyalTreeToFunction Y) :
    joyalPathRangeOrder X = joyalPathRangeOrder Y := by
  classical
  have hdom := joyalPathDomainOrder_eq_of_function_eq hXY
  apply List.ext_getElem
  · calc
      (joyalPathRangeOrder X).length = (joyalPathDomainOrder X).length :=
        (joyalPathOrders_length_eq X).symm
      _ = (joyalPathDomainOrder Y).length := by rw [hdom]
      _ = (joyalPathRangeOrder Y).length := joyalPathOrders_length_eq Y
  · intro i hx hy
    have hdx : i < (joyalPathDomainOrder X).length := by
      simpa [joyalPathOrders_length_eq X] using hx
    have hdy : i < (joyalPathDomainOrder Y).length := by
      simpa [joyalPathOrders_length_eq Y] using hy
    calc
      (joyalPathRangeOrder X)[i]'hx
          = joyalTreeToFunction X ((joyalPathDomainOrder X)[i]'hdx) :=
            joyalPathRangeOrder_get_eq_function_domain_get X i hx hdx
      _ = joyalTreeToFunction Y ((joyalPathDomainOrder Y)[i]'hdy) := by
            have harg : (joyalPathDomainOrder X)[i]'hdx =
                (joyalPathDomainOrder Y)[i]'hdy := by
              simp [hdom]
            rw [hXY, harg]
      _ = (joyalPathRangeOrder Y)[i]'hy :=
            (joyalPathRangeOrder_get_eq_function_domain_get Y i hy hdy).symm

theorem joyalPathRangeOrder_zero (X : DoublyRootedLabeledTree n)
    (h : 0 < (joyalPathRangeOrder X).length) :
    (joyalPathRangeOrder X)[0]'h = X.2.1 := by
  simp [joyalPathRangeOrder]

theorem joyalPathRangeOrder_length_pos (X : DoublyRootedLabeledTree n) :
    0 < (joyalPathRangeOrder X).length := by
  simp [joyalPathRangeOrder]

theorem joyalPathRangeOrder_last (X : DoublyRootedLabeledTree n)
    (h : 0 < (joyalPathRangeOrder X).length) :
    (joyalPathRangeOrder X)[(joyalPathRangeOrder X).length - 1]'(Nat.pred_lt (Nat.ne_of_gt h)) = X.2.2 := by
  simp [joyalPathRangeOrder, SimpleGraph.Walk.length_support]

theorem mem_joyalPathVertices_of_mem_treePath_to_left (X : DoublyRootedLabeledTree n)
    {z y : Fin n} (hz : z ∈ joyalPathVertices X)
    (hy : y ∈ (treePath X.1 z X.2.1).support) :
    y ∈ joyalPathVertices X := by
  classical
  let p := treePath X.1 X.2.1 X.2.2
  have hzsup : z ∈ p.support := by
    have hz' := hz
    simp [joyalPathVertices] at hz'
    exact hz'
  let q : X.1.1.Walk z X.2.1 := (p.takeUntil z hzsup).reverse
  have hqPath : q.IsPath := by
    exact ((treePath_isPath X.1 X.2.1 X.2.2).takeUntil hzsup).reverse
  have hqEq : q = treePath X.1 z X.2.1 := treePath_unique X.1 z X.2.1 hqPath
  have hyq : y ∈ q.support := by
    rwa [hqEq]
  have hytake : y ∈ (p.takeUntil z hzsup).support := by
    have hyq' := hyq
    simp [q, SimpleGraph.Walk.support_reverse] at hyq'
    exact hyq'
  have hyp : y ∈ p.support := SimpleGraph.Walk.support_takeUntil_subset p hzsup hytake
  change y ∈ p.support.toFinset
  exact List.mem_toFinset.mpr hyp

theorem not_offpath_adj_path_farther_from_left (X : DoublyRootedLabeledTree n)
    {w z : Fin n} (hw : w ∉ joyalPathVertices X) (hz : z ∈ joyalPathVertices X)
    (hadj : X.1.1.Adj w z)
    (hdist : X.1.1.dist X.2.1 w + 1 = X.1.1.dist X.2.1 z) :
    False := by
  classical
  let q := treePath X.1 w X.2.1
  let r : X.1.1.Walk z X.2.1 := SimpleGraph.Walk.cons hadj.symm q
  have hqLen : q.length = X.1.1.dist w X.2.1 := treePath_length_eq_dist X.1 w X.2.1
  have hrLen : r.length = X.1.1.dist z X.2.1 := by
    change q.length + 1 = X.1.1.dist z X.2.1
    rw [hqLen]
    rw [SimpleGraph.dist_comm (u := w) (v := X.2.1)]
    rw [SimpleGraph.dist_comm (u := z) (v := X.2.1)]
    exact hdist
  have hrPath : r.IsPath := SimpleGraph.Walk.isPath_of_length_eq_dist r hrLen
  have hrEq : treePath X.1 z X.2.1 = r := (treePath_unique X.1 z X.2.1 hrPath).symm
  have hwmem : w ∈ (treePath X.1 z X.2.1).support := by
    rw [hrEq]
    simp [r]
  exact hw (mem_joyalPathVertices_of_mem_treePath_to_left X hz hwmem)

theorem joyal_left_eq_of_function_eq {X Y : DoublyRootedLabeledTree n}
    (hXY : joyalTreeToFunction X = joyalTreeToFunction Y) :
    X.2.1 = Y.2.1 := by
  have hrange := joyalPathRangeOrder_eq_of_function_eq hXY
  have hX := joyalPathRangeOrder_length_pos X
  have hY := joyalPathRangeOrder_length_pos Y
  calc
    X.2.1 = (joyalPathRangeOrder X)[0]'hX := (joyalPathRangeOrder_zero X hX).symm
    _ = (joyalPathRangeOrder Y)[0]'hY := by simp [hrange]
    _ = Y.2.1 := joyalPathRangeOrder_zero Y hY

theorem joyal_right_eq_of_function_eq {X Y : DoublyRootedLabeledTree n}
    (hXY : joyalTreeToFunction X = joyalTreeToFunction Y) :
    X.2.2 = Y.2.2 := by
  have hrange := joyalPathRangeOrder_eq_of_function_eq hXY
  have hX := joyalPathRangeOrder_length_pos X
  have hY := joyalPathRangeOrder_length_pos Y
  have hlen : (joyalPathRangeOrder X).length = (joyalPathRangeOrder Y).length := by
    rw [hrange]
  calc
    X.2.2 =
        (joyalPathRangeOrder X)[(joyalPathRangeOrder X).length - 1]'(Nat.pred_lt (Nat.ne_of_gt hX)) :=
          (joyalPathRangeOrder_last X hX).symm
    _ = (joyalPathRangeOrder Y)[(joyalPathRangeOrder Y).length - 1]'(Nat.pred_lt (Nat.ne_of_gt hY)) := by
          simp [hrange]
    _ = Y.2.2 := joyalPathRangeOrder_last Y hY









theorem joyalRecoveredAdj_of_offpath_dist_left_add_one (X : DoublyRootedLabeledTree n)
    {w z : Fin n} (hw : w ∉ joyalPathVertices X) (hadj : X.1.1.Adj w z)
    (hdist : X.1.1.dist X.2.1 z + 1 = X.1.1.dist X.2.1 w) :
    joyalRecoveredAdj X w z := by
  right
  left
  refine ⟨hw, ?_⟩
  rw [joyalTreeToFunction_apply_of_not_mem X hw]
  exact joyalOffPathValue_eq_of_adj_dist_left_add_one X hw hadj hdist

theorem joyalRecoveredAdj_of_offpath_dist_left_add_one_right (X : DoublyRootedLabeledTree n)
    {w z : Fin n} (hw : w ∉ joyalPathVertices X) (hadj : X.1.1.Adj z w)
    (hdist : X.1.1.dist X.2.1 z + 1 = X.1.1.dist X.2.1 w) :
    joyalRecoveredAdj X z w := by
  right
  right
  refine ⟨hw, ?_⟩
  rw [joyalTreeToFunction_apply_of_not_mem X hw]
  exact joyalOffPathValue_eq_of_adj_dist_left_add_one X hw hadj.symm hdist





theorem adjacentInList_joyalPathRangeOrder_adj (X : DoublyRootedLabeledTree n)
    {u v : Fin n} (h : adjacentInList (joyalPathRangeOrder X) u v) :
    X.1.1.Adj u v := by
  classical
  let p := treePath X.1 X.2.1 X.2.2
  rcases h with ⟨i, hi, hi', huv | hvu⟩
  · have hilen : i < p.length := by
      have hi'p : i + 1 < p.support.length := by
        simpa [joyalPathRangeOrder, p] using hi'
      rw [SimpleGraph.Walk.length_support] at hi'p
      omega
    have hip : i < p.support.length := by
      simpa [joyalPathRangeOrder, p] using hi
    have hi'p : i + 1 < p.support.length := by
      simpa [joyalPathRangeOrder, p] using hi'
    have h0 : p.getVert i = u := by
      have hs := SimpleGraph.Walk.support_getElem_eq_getVert p hip
      have hsu : p.support[i]'hip = u := by
        simpa [joyalPathRangeOrder, p] using huv.1
      exact hs.symm.trans hsu
    have h1 : p.getVert (i + 1) = v := by
      have hs := SimpleGraph.Walk.support_getElem_eq_getVert p hi'p
      have hsv : p.support[i + 1]'hi'p = v := by
        simpa [joyalPathRangeOrder, p] using huv.2
      exact hs.symm.trans hsv
    simpa [h0, h1] using p.adj_getVert_succ (i := i) hilen
  · have hilen : i < p.length := by
      have hi'p : i + 1 < p.support.length := by
        simpa [joyalPathRangeOrder, p] using hi'
      rw [SimpleGraph.Walk.length_support] at hi'p
      omega
    have hip : i < p.support.length := by
      simpa [joyalPathRangeOrder, p] using hi
    have hi'p : i + 1 < p.support.length := by
      simpa [joyalPathRangeOrder, p] using hi'
    have h0 : p.getVert i = v := by
      have hs := SimpleGraph.Walk.support_getElem_eq_getVert p hip
      have hsv : p.support[i]'hip = v := by
        simpa [joyalPathRangeOrder, p] using hvu.1
      exact hs.symm.trans hsv
    have h1 : p.getVert (i + 1) = u := by
      have hs := SimpleGraph.Walk.support_getElem_eq_getVert p hi'p
      have hsu : p.support[i + 1]'hi'p = u := by
        simpa [joyalPathRangeOrder, p] using hvu.2
      exact hs.symm.trans hsu
    have hadj : X.1.1.Adj v u := by
      simpa [h0, h1] using p.adj_getVert_succ (i := i) hilen
    exact hadj.symm

theorem joyalRecoveredAdj_adj (X : DoublyRootedLabeledTree n)
    {u v : Fin n} (h : joyalRecoveredAdj X u v) :
    X.1.1.Adj u v := by
  classical
  rcases h with hpath | hoff | hoff
  · exact adjacentInList_joyalPathRangeOrder_adj X hpath
  · rcases hoff with ⟨hu, hfu⟩
    have hadj := joyalOffPathValue_adj X u hu
    rwa [← joyalTreeToFunction_apply_of_not_mem X hu, hfu] at hadj
  · rcases hoff with ⟨hv, hfv⟩
    have hadj := joyalOffPathValue_adj X v hv
    have hadj' : X.1.1.Adj v u := by
      rwa [← joyalTreeToFunction_apply_of_not_mem X hv, hfv] at hadj
    exact hadj'.symm

theorem joyalRecoveredAdj_eq_of_function_eq {X Y : DoublyRootedLabeledTree n}
    (hXY : joyalTreeToFunction X = joyalTreeToFunction Y) (u v : Fin n) :
    joyalRecoveredAdj X u v ↔ joyalRecoveredAdj Y u v := by
  have hpath := joyalPathVertices_eq_of_function_eq hXY
  have hrange := joyalPathRangeOrder_eq_of_function_eq hXY
  simp [joyalRecoveredAdj, hpath, hrange, hXY]

theorem joyalRecoveredAdj_of_path_edge (X : DoublyRootedLabeledTree n)
    {u v : Fin n} (hu : u ∈ joyalPathVertices X) (hv : v ∈ joyalPathVertices X)
    (hadj : X.1.1.Adj u v) :
    joyalRecoveredAdj X u v := by
  classical
  left
  let p := treePath X.1 X.2.1 X.2.2
  have huSup : u ∈ p.support := by
    simpa [joyalPathVertices, p] using hu
  have hvSup : v ∈ p.support := by
    simpa [joyalPathVertices, p] using hv
  let lu := (p.takeUntil u huSup).length
  let lv := (p.takeUntil v hvSup).length
  have hdistu : X.1.1.dist X.2.1 u = lu := by
    have hpath : (p.takeUntil u huSup).IsPath :=
      (treePath_isPath X.1 X.2.1 X.2.2).takeUntil huSup
    exact (isTree_path_length_eq_dist X.1 hpath).symm
  have hdistv : X.1.1.dist X.2.1 v = lv := by
    have hpath : (p.takeUntil v hvSup).IsPath :=
      (treePath_isPath X.1 X.2.1 X.2.2).takeUntil hvSup
    exact (isTree_path_length_eq_dist X.1 hpath).symm
  have hduv := X.1.2.dist_eq_dist_add_one_of_adj X.2.1 hadj
  rcases hduv with hdu | hdv
  · have hlu : lv + 1 = lu := by omega
    have hlvle : lv ≤ p.length := by
      simpa [lv] using p.length_takeUntil_le hvSup
    have hlule : lu ≤ p.length := by
      simpa [lu] using p.length_takeUntil_le huSup
    have hi : lv < p.support.length := by
      rw [SimpleGraph.Walk.length_support]
      omega
    have hi' : lv + 1 < p.support.length := by
      rw [SimpleGraph.Walk.length_support]
      omega
    have hvget : p.getVert lv = v := by
      simpa [lv] using SimpleGraph.Walk.getVert_length_takeUntil (p := p) hvSup
    have huget : p.getVert (lv + 1) = u := by
      rw [hlu]
      simpa [lu] using SimpleGraph.Walk.getVert_length_takeUntil (p := p) huSup
    refine ⟨lv, hi, hi', Or.inr ⟨?_, ?_⟩⟩
    · exact (SimpleGraph.Walk.support_getElem_eq_getVert p hi).trans hvget
    · exact (SimpleGraph.Walk.support_getElem_eq_getVert p hi').trans huget
  · have hlv : lu + 1 = lv := by omega
    have hlule : lu ≤ p.length := by
      simpa [lu] using p.length_takeUntil_le huSup
    have hlvle : lv ≤ p.length := by
      simpa [lv] using p.length_takeUntil_le hvSup
    have hi : lu < p.support.length := by
      rw [SimpleGraph.Walk.length_support]
      omega
    have hi' : lu + 1 < p.support.length := by
      rw [SimpleGraph.Walk.length_support]
      omega
    have huget : p.getVert lu = u := by
      simpa [lu] using SimpleGraph.Walk.getVert_length_takeUntil (p := p) huSup
    have hvget : p.getVert (lu + 1) = v := by
      rw [hlv]
      simpa [lv] using SimpleGraph.Walk.getVert_length_takeUntil (p := p) hvSup
    refine ⟨lu, hi, hi', Or.inl ⟨?_, ?_⟩⟩
    · exact (SimpleGraph.Walk.support_getElem_eq_getVert p hi).trans huget
    · exact (SimpleGraph.Walk.support_getElem_eq_getVert p hi').trans hvget

/--
The Joyal endofunction data reconstructs the original tree edges: consecutive
vertices on the left-right path give the path edges, and every off-path vertex
is connected to its image.
-/
theorem joyal_tree_adj_iff_recovered (X : DoublyRootedLabeledTree n) (u v : Fin n) :
    X.1.1.Adj u v ↔ joyalRecoveredAdj X u v := by
  classical
  constructor
  · intro h
    have hdist := X.1.2.dist_eq_dist_add_one_of_adj X.2.1 h
    rcases hdist with hdu | hdv
    · by_cases hu : u ∈ joyalPathVertices X
      · by_cases hv : v ∈ joyalPathVertices X
        · exact joyalRecoveredAdj_of_path_edge X hu hv h
        · exact False.elim <|
            not_offpath_adj_path_farther_from_left X hv hu h.symm hdu.symm
      · exact joyalRecoveredAdj_of_offpath_dist_left_add_one X hu h hdu.symm
    · by_cases hv : v ∈ joyalPathVertices X
      · by_cases hu : u ∈ joyalPathVertices X
        · exact joyalRecoveredAdj_of_path_edge X hu hv h
        · exact False.elim <|
            not_offpath_adj_path_farther_from_left X hu hv h hdv.symm
      · exact joyalRecoveredAdj_of_offpath_dist_left_add_one_right X hv h hdv.symm
  · exact joyalRecoveredAdj_adj X

theorem joyal_tree_eq_of_function_eq {X Y : DoublyRootedLabeledTree n}
    (hXY : joyalTreeToFunction X = joyalTreeToFunction Y) :
    X.1 = Y.1 := by
  apply Subtype.ext
  ext u v
  rw [joyal_tree_adj_iff_recovered X u v, joyal_tree_adj_iff_recovered Y u v]
  exact joyalRecoveredAdj_eq_of_function_eq hXY u v

theorem joyalTreeToFunction_injective (n : ℕ) :
    Function.Injective (joyalTreeToFunction : DoublyRootedLabeledTree n → Fin n → Fin n) := by
  intro X Y hXY
  cases X with
  | mk XT Xroots =>
    cases Xroots with
    | mk Xleft Xright =>
      cases Y with
      | mk YT Yroots =>
        cases Yroots with
        | mk Yleft Yright =>
          have htree : XT = YT := joyal_tree_eq_of_function_eq hXY
          have hleft : Xleft = Yleft := joyal_left_eq_of_function_eq hXY
          have hright : Xright = Yright := joyal_right_eq_of_function_eq hXY
          subst htree
          subst hleft
          subst hright
          rfl

theorem doublyRootedLabeledTree_card (n : ℕ) :
    Fintype.card (DoublyRootedLabeledTree n) = Fintype.card (LabeledTree n) * n * n := by
  simp [DoublyRootedLabeledTree, Nat.mul_assoc]

theorem endofunction_card (n : ℕ) :
    Fintype.card (Fin n → Fin n) = n ^ n := by
  simp

/--
The numerical part of Joyal's proof: an injection from doubly-rooted labeled trees
to endofunctions on `Fin n` implies Cayley's upper bound.
-/
theorem cayley_upper_bound_of_joyal_injection (n : ℕ) (hn : 2 ≤ n)
    (hcard : Fintype.card (DoublyRootedLabeledTree n) ≤ Fintype.card (Fin n → Fin n)) :
    Fintype.card (LabeledTree n) ≤ n ^ (n - 2) := by
  rw [doublyRootedLabeledTree_card, endofunction_card] at hcard
  have hnpos : 0 < n := by omega
  have hfactor_pos : 0 < n * n := Nat.mul_pos hnpos hnpos
  have hpow : n ^ n = n ^ (n - 2) * (n * n) := by
    calc
      n ^ n = n ^ ((n - 2) + 2) := by congr; omega
      _ = n ^ (n - 2) * n ^ 2 := by rw [pow_add]
      _ = n ^ (n - 2) * (n * n) := by rw [pow_two]
  have hmul : Fintype.card (LabeledTree n) * (n * n) ≤ n ^ (n - 2) * (n * n) := by
    simpa [Nat.mul_assoc, hpow] using hcard
  exact Nat.le_of_mul_le_mul_right hmul hfactor_pos

/--
Joyal's theorem specialized to the direction needed here.  The book constructs
a bijection between endofunctions on `Fin n` and doubly-rooted labeled trees;
this cardinal inequality is the remaining formal content of that bijection.
-/
theorem joyal_doubly_rooted_card_bound (n : ℕ) :
    Fintype.card (DoublyRootedLabeledTree n) ≤ Fintype.card (Fin n → Fin n) := by
  classical
  exact Fintype.card_le_of_injective joyalTreeToFunction (joyalTreeToFunction_injective n)

/-!
### Current target: eliminate the Cayley upper-bound premise

The book chapter (Chapter 30 in `proofs_in_the_book.pdf`, Chapter31 in this
repository) mentions Prüfer's code, then develops several alternate proofs:
Joyal's function-to-doubly-rooted-tree bijection, Kirchhoff's matrix-tree
proof, Riordan-Rényi recursion, and Pitman's double-counting proof for rooted
forests.

For this Lean file the immediate target is the upper bound needed to construct
an injection into Prüfer code space:

`Fintype.card (LabeledTree n) ≤ n ^ (n - 2)`.

This is isolated here as the single remaining mathematical target for the
chapter. The likely formalization route is still under evaluation:

* Prüfer encoding uses Mathlib's `SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial`
  and leaf deletion lemmas.
* The book's Joyal/Pitman proofs may avoid recursive graph deletion but require
  formalizing functional digraph cycles or rooted forests.
-/
theorem cayley_upper_bound (n : ℕ) (_hn : 2 ≤ n) :
    Fintype.card (LabeledTree n) ≤ n ^ (n - 2) := by
  classical
  exact cayley_upper_bound_of_joyal_injection n _hn (joyal_doubly_rooted_card_bound n)









































































/-! Ch31 Tier 2: degree formula for the decoded forest. -/





























/-- The smallest tree-leaf of `pruferDecode s` equals the smallest vertex not
appearing in `s`, which is `nextLeaf_0` from the decode process. -/
theorem smallestTreeLeaf_pruferDecode (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    smallestTreeLeaf n hn (pruferDecode hn s) =
    (Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v)).min'
      (by
        have h0_le : 0 ≤ n - 2 := Nat.zero_le _
        have h_nonempty := nextLeaf_nonempty hn s 0 h0_le Finset.univ (by simp)
        have h_finsets : Finset.univ.filter (fun v => ∀ j : Fin (n - 2), 0 ≤ j.val → s j ≠ v) =
                         Finset.univ.filter (fun v => ∀ j : Fin (n - 2), s j ≠ v) := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h j => h j (Nat.zero_le _), fun h j _ => h j⟩
        rw [h_finsets] at h_nonempty
        exact h_nonempty) := by
  have h_eq : treeLeaves (pruferDecode hn s) = Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v) := by
    ext v
    rw [pruferDecode_isLeaf_iff n hn s v]
    unfold isLeafInPrufer
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold smallestTreeLeaf
  congr

private theorem smallestTreeLeaf_eq_min_filter (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    smallestTreeLeaf n hn (pruferDecode hn s) ∈
    (Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v)) ∧
    ∀ v ∈ (Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v)),
      smallestTreeLeaf n hn (pruferDecode hn s) ≤ v := by
  have h_eq := smallestTreeLeaf_pruferDecode n hn s
  rw [h_eq]
  exact ⟨Finset.min'_mem _ _, fun v hv => Finset.min'_le _ _ hv⟩

lemma step_one_edge_mem (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) (hge : 3 ≤ n) (e : Sym2 (Fin n))
    (he : e ∈ (pruferDecodeAux hn s 1 (by omega)).val.2) :
    e ∈ pruferDecodeEdges hn s := by
  have h_mono : ∀ m (h_ge1 : 1 ≤ m) (hm_le : m ≤ n - 2), e ∈ (pruferDecodeAux hn s m hm_le).val.2 := by
    intro m
    induction m with
    | zero => intro h1 _; omega
    | succ m ih =>
      intro h_ge hm_le
      by_cases h_eq : m = 0
      · subst h_eq
        have h_rw : (pruferDecodeAux hn s 1 (by omega)).val.2 = (pruferDecodeAux hn s 1 hm_le).val.2 := rfl
        rw [← h_rw]
        exact he
      · have hm_ge1 : 1 ≤ m := by omega
        have hm_le_prev : m ≤ n - 2 := by omega
        have ih_m := ih hm_ge1 hm_le_prev
        have h_succ : m + 1 ≤ n - 2 := hm_le
        obtain ⟨_, _, _, h_edges, _⟩ := pruferDecodeAux_succ_val_2 hn s m h_succ
        have h_rw : (pruferDecodeAux hn s (m + 1) hm_le).val.2 = (pruferDecodeAux hn s (m + 1) h_succ).val.2 := rfl
        rw [h_rw, h_edges]
        exact Finset.mem_insert_of_mem ih_m
  have h_in_n2 := h_mono (n - 2) (by omega) (by rfl)
  unfold pruferDecodeEdges
  exact Finset.mem_insert_of_mem h_in_n2

theorem smallestTreeLeafNeighbor_pruferDecode (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (hge : 3 ≤ n) :
    smallestTreeLeafNeighbor n hn (pruferDecode hn s) = s ⟨0, by omega⟩ := by
  set v := smallestTreeLeaf n hn (pruferDecode hn s)
  have h1 : 0 + 1 ≤ n - 2 := by omega
  have hv_min : v = (Finset.univ.filter (fun x => ∀ j : Fin (n - 2), 0 ≤ j.val → s j ≠ x)).min' (nextLeaf_nonempty hn s 0 (by omega) Finset.univ (by simp)) := by
    apply le_antisymm
    · apply Finset.le_min'
      intro y hy
      have hv_le : ∀ x ∈ Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v), v ≤ x :=
        (smallestTreeLeaf_eq_min_filter n hn s).2
      apply hv_le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      intro j
      exact hy j (Nat.zero_le _)
    · apply Finset.min'_le
      have hv_mem : v ∈ Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v) :=
        (smallestTreeLeaf_eq_min_filter n hn s).1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv_mem ⊢
      intro j _
      exact hv_mem j
  have h_step1 : (pruferDecodeAux hn s 1 h1).val.2 = {s(v, s ⟨0, by omega⟩)} := by
    dsimp [pruferDecodeAux]
    congr 2
    exact hv_min.symm
  have he : s(v, s ⟨0, by omega⟩) ∈ (pruferDecodeAux hn s 1 h1).val.2 := by
    rw [h_step1]
    exact Finset.mem_singleton_self _
  have he_rewrite : s(v, s ⟨0, by omega⟩) ∈ (pruferDecodeAux hn s 1 (by omega)).val.2 := by
    -- we can just change the proof of hm_le
    have h_rw : (pruferDecodeAux hn s 1 h1).val.2 = (pruferDecodeAux hn s 1 (by omega)).val.2 := rfl
    rw [← h_rw]
    exact he
  have h_in_final := step_one_edge_mem n hn s hge _ he_rewrite
  have h_adj : (fromEdgeSet (V := Fin n) (pruferDecodeEdges hn s : Set (Sym2 (Fin n)))).Adj v (s ⟨0, by omega⟩) := by
    rw [fromEdgeSet_adj]
    refine ⟨by exact_mod_cast h_in_final, ?_⟩
    have hv_mem : v ∈ Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v) :=
      (smallestTreeLeaf_eq_min_filter n hn s).1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv_mem
    exact (hv_mem ⟨0, by omega⟩).symm

  have h_deg : ((pruferDecode hn s).1).degree v = 1 := by
    have h_leaf : v ∈ treeLeaves (pruferDecode hn s) := Finset.min'_mem _ _
    rw [pruferDecode_isLeaf_iff n hn s v] at h_leaf
    rw [pruferDecode_degree n hn s v]
    have h_occur : countOccurrences s (n - 2) v = 0 := by
      unfold countOccurrences
      rw [Finset.card_eq_zero]
      ext j
      simp [h_leaf j]
    rw [h_occur]

  have h_adj' : ((pruferDecode hn s).1).Adj v (s ⟨0, by omega⟩) := h_adj
  exact (smallestTreeLeaf_neighbor_unique n hn (pruferDecode hn s) h_adj').symm

theorem pruferEncode_pruferDecode_zero (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (hge : 3 ≤ n) :
    (pruferEncode hn (pruferDecode hn s)) ⟨0, by omega⟩ = s ⟨0, by omega⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  show (pruferEncodeAux m (pruferDecode _ s)) ⟨0, by omega⟩ = s ⟨0, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  show smallestTreeLeafNeighbor (m' + 3) _ (pruferDecode _ s) = s ⟨0, by omega⟩
  exact smallestTreeLeafNeighbor_pruferDecode (m' + 3) _ s (by omega)









lemma min'_congr {α : Type} [LinearOrder α] {S1 S2 : Finset α} (h : S1 = S2)
    (h1 : S1.Nonempty) (h2 : S2.Nonempty) : S1.min' h1 = S2.min' h2 := by
  subst h
  rfl

lemma min'_commutes_L {m : ℕ} (nL : Fin (m + 2))
    (S : Finset (Fin (m + 1))) (h_nonempty : S.Nonempty) :
    (finSuccAboveEquivCompl nL (S.min' h_nonempty)).1 = (S.image (fun v => (finSuccAboveEquivCompl nL v).1)).min' (Finset.Nonempty.image h_nonempty _) := by
  apply le_antisymm
  · apply Finset.le_min'
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    have h_le : S.min' h_nonempty ≤ v := Finset.min'_le _ _ hv
    exact StrictMono.monotone (Fin.strictMono_succAbove nL) h_le
  · apply Finset.min'_le
    simp only [Finset.mem_image]
    exact ⟨S.min' h_nonempty, Finset.min'_mem _ _, rfl⟩

lemma pruferDecodeAux_succ_step {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (k : ℕ) (hk : k + 1 ≤ n - 2) :
    let state := (pruferDecodeAux hn s k (by omega)).val
    let nL := (state.1.filter (fun v => ∀ j : Fin (n - 2), k ≤ j.val → s j ≠ v)).min' (nextLeaf_nonempty hn s k (by omega) state.1 (pruferDecodeAux hn s k (by omega)).property.2.1)
    let si := s ⟨k, by omega⟩
    (pruferDecodeAux hn s (k + 1) hk).val = (state.1.erase nL, insert s(nL, si) state.2) := rfl

private lemma nextLeaf_correspond_lift {m : ℕ} (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)) (k : ℕ)
    (hk : k + 1 ≤ m + 1 - 2)
    (ih_avail : ∀ v : Fin (m + 1),
       v ∈ (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k (by omega)).val.1 ↔
       (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) v).1 ∈ (pruferDecodeAux (by omega) s (k + 1) (by omega)).val.1) :
    let state_shifted := (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k (by omega)).val
    let state_orig := (pruferDecodeAux (by omega) s (k + 1) (by omega)).val
    let nL_k := (state_shifted.1.filter
      (fun v => ∀ j : Fin (m + 1 - 2), k ≤ j.val → shiftedCode_v2 hm s j ≠ v)).min'
      (nextLeaf_nonempty (by omega) (shiftedCode_v2 hm s) k (by omega) state_shifted.1 (pruferDecodeAux (by omega) _ k (by omega)).property.2.1)
    let nL_k' := (state_orig.1.filter
      (fun v => ∀ j : Fin (m + 2 - 2), k + 1 ≤ j.val → s j ≠ v)).min'
      (nextLeaf_nonempty (by omega) s (k + 1) (by omega) state_orig.1 (pruferDecodeAux (by omega) s (k + 1) (by omega)).property.2.1)
    (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) nL_k).1 = nL_k' := by
  intro state_shifted state_orig nL_k nL_k'
  let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)
  let S := state_shifted.1.filter (fun v => ∀ j : Fin (m + 1 - 2), k ≤ j.val → shiftedCode_v2 hm s j ≠ v)
  let S' := state_orig.1.filter (fun v => ∀ j : Fin (m + 2 - 2), k + 1 ≤ j.val → s j ≠ v)
  have h_card_shifted : state_shifted.1.card = m + 1 - k := (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k (by omega)).property.2.1
  have h_card_orig : state_orig.1.card = m + 1 - k := by
    have h : state_orig.1.card = m + 2 - (k + 1) := (pruferDecodeAux (by omega) s (k + 1) (by omega)).property.2.1
    omega
  have h_img : state_shifted.1.image (fun v => (L v).1) = state_orig.1 := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ih_avail y |>.mp hy
    · rw [Finset.card_image_of_injective]
      · omega
      · intro y1 y2 h_eq
        have h_L : L y1 = L y2 := Subtype.ext h_eq
        exact Equiv.injective L h_L
  have h_S_eq : S.image (fun v => (L v).1) = S' := by
    ext x
    dsimp [S, S']
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨y, ⟨hy_avail, hy_not_in⟩, rfl⟩
      refine ⟨ih_avail y |>.mp hy_avail, ?_⟩
      intro j hj
      let j' : Fin (m + 1 - 2) := ⟨j.val - 1, by omega⟩
      have hj_val : j'.val = j.val - 1 := rfl
      have hj' : k ≤ j'.val := by omega
      have hy_not := hy_not_in j' hj'
      have h_shift_eval : (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) (shiftedCode_v2 hm s j')).1 = s j := by
        have h_j_eq : (⟨j'.val + 1, by omega⟩ : Fin (m + 2 - 2)) = j := by
          apply Fin.ext
          change j'.val + 1 = j.val
          omega
        dsimp [shiftedCode_v2]
        simp only [Equiv.apply_symm_apply]
        rw [h_j_eq]
      intro h_eq
      rw [← h_shift_eval] at h_eq
      have h_eq2 : L (shiftedCode_v2 hm s j') = L y := Subtype.ext h_eq
      have h_eq3 : shiftedCode_v2 hm s j' = y := Equiv.injective L h_eq2
      exact hy_not h_eq3
    · rintro ⟨hx_avail, hx_not_in⟩
      have hx_img : x ∈ state_shifted.1.image (fun v => (L v).1) := by
        rw [h_img]
        exact hx_avail
      simp only [Finset.mem_image] at hx_img
      obtain ⟨y, hy_avail, rfl⟩ := hx_img
      refine ⟨y, ⟨hy_avail, ?_⟩, rfl⟩
      intro j' hj'
      let j : Fin (m + 2 - 2) := ⟨j'.val + 1, by omega⟩
      have hj_val : j.val = j'.val + 1 := rfl
      have hj : k + 1 ≤ j.val := by omega
      have hx_not := hx_not_in j hj
      have h_shift_eval : (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) (shiftedCode_v2 hm s j')).1 = s j := by
        have h_j_eq : (⟨j'.val + 1, by omega⟩ : Fin (m + 2 - 2)) = j := by
          apply Fin.ext
          change j'.val + 1 = j.val
          omega
        dsimp [shiftedCode_v2]
        simp only [Equiv.apply_symm_apply]
        rw [h_j_eq]
      intro h_eq
      rw [h_eq] at h_shift_eval
      exact hx_not h_shift_eval.symm
  have h_min := min'_commutes_L (nextLeaf0 (by omega) s) S (nextLeaf_nonempty (by omega) (shiftedCode_v2 hm s) k (by omega) state_shifted.1 (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k (by omega)).property.2.1)
  rw [h_min]
  apply le_antisymm
  · apply Finset.le_min'
    intro y hy
    have h_eq_elem := Finset.ext_iff.mp h_S_eq y
    have hy_img := h_eq_elem.mpr hy
    exact Finset.min'_le _ _ hy_img
  · apply Finset.min'_le
    have h_nonempty_S' : S'.Nonempty := nextLeaf_nonempty (by omega) s (k + 1) (by omega) state_orig.1 (pruferDecodeAux (by omega) s (k + 1) (by omega)).property.2.1
    have h_nonempty_S_img : (S.image (fun v => (L v).1)).Nonempty := by
      rw [h_S_eq]
      exact h_nonempty_S'
    have h_mem := Finset.min'_mem (S.image (fun v => (L v).1)) h_nonempty_S_img
    have h_eq_elem := Finset.ext_iff.mp h_S_eq ((S.image (fun v => (L v).1)).min' h_nonempty_S_img)
    exact h_eq_elem.mp h_mem

lemma step_zero_min_eq_nextLeaf0 {m : ℕ} (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)) :
    ((pruferDecodeAux (by omega) s 0 (by omega)).val.1.filter (fun v => ∀ j : Fin (m + 2 - 2), 0 ≤ j.val → s j ≠ v)).min' (nextLeaf_nonempty (by omega) s 0 (by omega) (pruferDecodeAux (by omega) s 0 (by omega)).val.1 (pruferDecodeAux (by omega) s 0 (by omega)).property.2.1) = nextLeaf0 (by omega) s := by
  have h_val : (pruferDecodeAux (by omega) s 0 (by omega)).val.1 = Finset.univ := rfl
  have h_S : ((pruferDecodeAux (by omega) s 0 (by omega)).val.1.filter (fun v => ∀ j : Fin (m + 2 - 2), 0 ≤ j.val → s j ≠ v)) = Finset.univ.filter (fun v => ∀ j : Fin (m + 2 - 2), s j ≠ v) := by
    rw [h_val]
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j
      exact h j (by omega)
    · intro h j _
      exact h j
  dsimp [nextLeaf0, smallestTreeLeaf]
  apply le_antisymm
  · apply Finset.le_min'
    intro y hy
    rw [pruferDecode_isLeaf_iff] at hy
    have h_univ : y ∈ Finset.univ.filter (fun v => ∀ j : Fin (m + 2 - 2), s j ≠ v) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hy
    have hy' := Finset.ext_iff.mp h_S y |>.mpr h_univ
    exact Finset.min'_le _ _ hy'
  · apply Finset.min'_le
    set m_elem := ((pruferDecodeAux (by omega) s 0 (by omega)).val.1.filter (fun v => ∀ j : Fin (m + 2 - 2), 0 ≤ j.val → s j ≠ v)).min' (nextLeaf_nonempty (by omega) s 0 (by omega) (pruferDecodeAux (by omega) s 0 (by omega)).val.1 (pruferDecodeAux (by omega) s 0 (by omega)).property.2.1)
    have hy := Finset.min'_mem _ (nextLeaf_nonempty (by omega) s 0 (by omega) (pruferDecodeAux (by omega) s 0 (by omega)).val.1 (pruferDecodeAux (by omega) s 0 (by omega)).property.2.1)
    have h_univ : m_elem ∈ Finset.univ.filter (fun v => ∀ j : Fin (m + 2 - 2), s j ≠ v) := Finset.ext_iff.mp h_S m_elem |>.mp hy
    rw [Finset.mem_filter] at h_univ
    rw [pruferDecode_isLeaf_iff]
    exact h_univ.2

private theorem pruferDecodeAux_shifted_correspondence {m : ℕ} (hm : 1 ≤ m)
    (s : pruferCodeSpace (m + 2)) :
    ∀ (k : ℕ) (hk : k ≤ (m + 1) - 2),
    (∀ v : Fin (m + 1),
       v ∈ (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk).val.1 ↔
       (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) v).1
         ∈ (pruferDecodeAux (by omega) s (k + 1) (by omega)).val.1) ∧
    (∀ a b : Fin (m + 1),
       s(a, b) ∈ (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk).val.2 ↔
       s((finSuccAboveEquivCompl (nextLeaf0 (by omega) s) a).1,
          (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) b).1)
         ∈ (pruferDecodeAux (by omega) s (k + 1) (by omega)).val.2) := by
  intro k
  induction k with
  | zero =>
    intro hk
    constructor
    · intro v
      have h_step_orig := pruferDecodeAux_succ_step (by omega) s 0 (by omega)
      have h_state0_orig : (pruferDecodeAux (by omega) s 0 (by omega)).val = (Finset.univ, ∅) := rfl
      have h_state0_shift : (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) 0 hk).val = (Finset.univ, ∅) := rfl
      have h_nL_eq := step_zero_min_eq_nextLeaf0 hm s
      let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)
      rw [h_state0_shift]
      have h_orig1 : (pruferDecodeAux (by omega) s 1 (by omega)).val.1 = Finset.univ.erase (nextLeaf0 (by omega) s) := by
        rw [h_step_orig]
        dsimp
        rw [h_nL_eq]
        rw [h_state0_orig]
      rw [h_orig1]
      simp only [Finset.mem_univ, Finset.mem_erase, ne_eq, and_true]
      exact iff_of_true trivial (L v).property
    · intro a b
      have h_step_orig := pruferDecodeAux_succ_step (by omega) s 0 (by omega)
      have h_state0_orig : (pruferDecodeAux (by omega) s 0 (by omega)).val = (Finset.univ, ∅) := rfl
      have h_state0_shift : (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) 0 hk).val = (Finset.univ, ∅) := rfl
      have h_nL_eq := step_zero_min_eq_nextLeaf0 hm s
      let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)
      rw [h_state0_shift]
      have h_orig1 : (pruferDecodeAux (by omega) s 1 (by omega)).val.2 = {s(nextLeaf0 (by omega) s, s ⟨0, by omega⟩)} := by
        rw [h_step_orig]
        dsimp
        rw [h_nL_eq]
        rw [h_state0_orig]
        rfl
      rw [h_orig1]
      simp only [Finset.mem_singleton, Sym2.eq_iff]
      constructor
      · intro h_empty
        revert h_empty
        simp
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact (L a).property h1 |>.elim
        · exact (L b).property h2 |>.elim
  | succ k ih =>
    intro hk
    have hm1 : m + 1 - 2 = m - 1 := by omega
    have hm2 : m + 2 - 2 = m := by omega
    have hk_curr : k + 1 ≤ m + 1 - 2 := hk
    have hk_prev : k ≤ m + 1 - 2 := by omega
    have hk_next : k + 2 ≤ m + 2 - 2 := by omega
    have hk_next_orig : k + 1 ≤ m + 2 - 2 := by omega
    have ih_k := ih hk_prev
    have ih_avail := ih_k.1
    have ih_edges := ih_k.2

    let state_shifted := (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk_prev).val
    let state_orig := (pruferDecodeAux (by omega) s (k + 1) hk_next_orig).val
    let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)

    have h_step_shift := pruferDecodeAux_succ_step (by omega) (shiftedCode_v2 hm s) k hk_curr
    have h_step_orig := pruferDecodeAux_succ_step (by omega) s (k + 1) hk_next

    have h_nL_eq := nextLeaf_correspond_lift hm s k hk_curr ih_avail
    have h_nonempty_shift := nextLeaf_nonempty (by omega) (shiftedCode_v2 hm s) k hk_prev state_shifted.1 (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk_prev).property.2.1
    have h_nonempty_orig := nextLeaf_nonempty (by omega) s (k + 1) hk_next_orig state_orig.1 (pruferDecodeAux (by omega) s (k + 1) hk_next_orig).property.2.1
    set nL_k := (state_shifted.1.filter (fun v => ∀ j : Fin (m + 1 - 2), k ≤ j.val → shiftedCode_v2 hm s j ≠ v)).min' h_nonempty_shift
    set nL_k' := (state_orig.1.filter (fun v => ∀ j : Fin (m + 2 - 2), k + 1 ≤ j.val → s j ≠ v)).min' h_nonempty_orig
    have h_L_nL : (L nL_k).1 = nL_k' := h_nL_eq

    constructor
    · intro v
      have h_shift_val : (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) (k + 1) hk_curr).val.1 = state_shifted.1.erase nL_k := by
        rw [h_step_shift]
      have h_orig_val : (pruferDecodeAux (by omega) s (k + 2) hk_next).val.1 = state_orig.1.erase nL_k' := by
        rw [h_step_orig]
      rw [h_shift_val, h_orig_val]
      simp only [Finset.mem_erase, ne_eq]
      rw [ih_avail v]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        intro h_eq
        have h_L_eq : (L v).1 = (L nL_k).1 := by
          rw [h_eq, h_L_nL]
        have h_v_eq := Equiv.injective L (Subtype.ext h_L_eq)
        exact h1 h_v_eq
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        intro h_eq
        have h_L_eq : (L v).1 = nL_k' := by
          rw [h_eq, h_L_nL]
        exact h1 h_L_eq
    · intro a b
      have h_shift_val : (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) (k + 1) hk_curr).val.2 = insert s(nL_k, shiftedCode_v2 hm s ⟨k, by omega⟩) state_shifted.2 := by
        rw [h_step_shift]
      have h_orig_val : (pruferDecodeAux (by omega) s (k + 2) hk_next).val.2 = insert s(nL_k', s ⟨k + 1, by omega⟩) state_orig.2 := by
        rw [h_step_orig]
      rw [h_shift_val, h_orig_val]
      rw [Finset.mem_insert, Finset.mem_insert]
      rw [ih_edges a b]
      have hk_lt1 : k < m + 1 - 2 := by omega
      have hk_lt2 : k + 1 < m + 2 - 2 := by omega
      have h_shift_code_eval : (L (shiftedCode_v2 hm s ⟨k, hk_lt1⟩)).1 = s ⟨k + 1, hk_lt2⟩ := by
        dsimp [L, shiftedCode_v2]
        simp only [Equiv.apply_symm_apply]
      have h_edge_eq : s((L a).1, (L b).1) = s(nL_k', s ⟨k + 1, hk_lt2⟩) ↔ s(a, b) = s(nL_k, shiftedCode_v2 hm s ⟨k, hk_lt1⟩) := by
        simp only [Sym2.eq_iff]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · left
            constructor
            · have h_ext : L a = L nL_k := Subtype.ext (by rw [h1, ← h_L_nL])
              exact Equiv.injective L h_ext
            · have h_ext : L b = L (shiftedCode_v2 hm s ⟨k, by omega⟩) := Subtype.ext (by rw [h2, ← h_shift_code_eval])
              exact Equiv.injective L h_ext
          · right
            constructor
            · have h_ext : L a = L (shiftedCode_v2 hm s ⟨k, by omega⟩) := Subtype.ext (by rw [h1, ← h_shift_code_eval])
              exact Equiv.injective L h_ext
            · have h_ext : L b = L nL_k := Subtype.ext (by rw [h2, ← h_L_nL])
              exact Equiv.injective L h_ext
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · left
            constructor
            · rw [h1, h_L_nL]
            · rw [h2, h_shift_code_eval]
          · right
            constructor
            · rw [h1, h_shift_code_eval]
            · rw [h2, h_L_nL]
      rw [h_edge_eq]

lemma deleteSmallestLeafTreeSucc_val_adj {m : ℕ} (hm : 1 ≤ m) (T : LabeledTree (m + 1)) (a b : Fin m) :
    (↑(deleteSmallestLeafTreeSucc m hm T) : SimpleGraph (Fin m)).Adj a b ↔
    (↑T : SimpleGraph (Fin (m + 1))).Adj ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) a).1
            ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) b).1 := by
  dsimp [deleteSmallestLeafTreeSucc]
  simp only [SimpleGraph.comap_adj]
  have h_a : ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) a).1 ≠ smallestTreeLeaf (m + 1) (by omega) T :=
    ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) a).2
  have h_b : ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) b).1 ≠ smallestTreeLeaf (m + 1) (by omega) T :=
    ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) b).2
  tauto

lemma pruferDecodeAux_val_1_congr {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) {k1 k2 : ℕ} (hk1 : k1 ≤ n - 2) (hk2 : k2 ≤ n - 2) (h : k1 = k2) :
    (pruferDecodeAux hn s k1 hk1).val.1 = (pruferDecodeAux hn s k2 hk2).val.1 := by
  subst h; rfl

lemma pruferDecodeAux_val_2_congr {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) {k1 k2 : ℕ} (hk1 : k1 ≤ n - 2) (hk2 : k2 ≤ n - 2) (h : k1 = k2) :
    (pruferDecodeAux hn s k1 hk1).val.2 = (pruferDecodeAux hn s k2 hk2).val.2 := by
  subst h; rfl

lemma pruferDecodeAux_val_1_subset {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) {k1 k2 : ℕ} (hk1 : k1 ≤ n - 2) (hk2 : k2 ≤ n - 2) (hle : k1 ≤ k2) :
    (pruferDecodeAux hn s k2 hk2).val.1 ⊆ (pruferDecodeAux hn s k1 hk1).val.1 := by
  revert hk2
  induction hle with
  | refl =>
    intro hk2 x hx
    exact hx
  | @step k_mid h_le ih =>
    intro hk2
    have hk_succ : k_mid + 1 ≤ n - 2 := hk2
    have hk_mid : k_mid ≤ n - 2 := by omega
    have h_ih := ih hk_mid
    have h_eq := pruferDecodeAux_succ_step hn s k_mid hk_succ
    have h_c := pruferDecodeAux_val_1_congr hn s (by omega : k_mid + 1 ≤ n - 2) hk2 rfl
    rw [← h_c]
    have h_val : (pruferDecodeAux hn s (k_mid + 1) hk_succ).val.1 = (pruferDecodeAux hn s k_mid hk_mid).val.1.erase _ := congrArg Prod.fst h_eq
    rw [h_val]
    intro x hx
    have h_erase := Finset.erase_subset _ _ hx
    exact h_ih h_erase

theorem deleteSmallestLeaf_pruferDecode_v2 {m : ℕ} (hm : 1 ≤ m)
    (s : pruferCodeSpace (m + 2)) :
    deleteSmallestLeafTreeSucc (m + 1) (by omega) (pruferDecode (by omega) s) =
    pruferDecode (by omega : 2 ≤ m + 1) (shiftedCode_v2 hm s) := by
  ext a b
  let shift_s := shiftedCode_v2 hm s
  have hn_shift : 2 ≤ m + 1 := by omega
  have hn_s : 2 ≤ m + 2 := by omega
  have hm_sub : m - 1 ≤ (m + 1) - 2 := by omega
  have h_corr := pruferDecodeAux_shifted_correspondence hm s (m - 1) hm_sub
  have h_corr_v := h_corr.1
  have h_corr_e := h_corr.2

  have h_state_shift : (pruferFinalState hn_shift shift_s).1 = (pruferDecodeAux hn_shift shift_s (m - 1) hm_sub).val.1 := rfl
  have h_state_s : (pruferFinalState hn_s s).1 = (pruferDecodeAux hn_s s m (by omega)).val.1 := by
    have h_idx : m + 2 - 2 = m := by omega
    exact pruferDecodeAux_val_1_congr hn_s s (by omega) (by omega) h_idx

  have h_image_eq : (pruferFinalState hn_shift shift_s).1.image (fun v => (finSuccAboveEquivCompl (nextLeaf0 hn_s s) v).1) = (pruferFinalState hn_s s).1 := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have h_corr_v_spec := h_corr_v v
      have h_s_eq : (pruferDecodeAux hn_s s (m - 1 + 1) (by omega)).val.1 = (pruferFinalState hn_s s).1 := by
        have h_idx : m - 1 + 1 = m + 2 - 2 := by omega
        exact pruferDecodeAux_val_1_congr hn_s s (by omega) (by omega) h_idx
      rw [h_s_eq] at h_corr_v_spec
      exact h_corr_v_spec.mp hv
    · intro hx
      have h_not_nL : x ≠ nextLeaf0 hn_s s := by
        have h_leaf_mem : nextLeaf0 hn_s s ∈ (pruferDecodeAux hn_s s 0 (by omega)).val.1 := Finset.mem_univ _
        have h_not_in_final : nextLeaf0 hn_s s ∉ (pruferFinalState hn_s s).1 := by
          have h_s_eq : (pruferFinalState hn_s s).1 = (pruferDecodeAux hn_s s (m + 2 - 2) (by omega)).val.1 := rfl
          rw [h_s_eq]
          have h_erase : (pruferDecodeAux hn_s s 1 (by omega)).val.1 = Finset.univ.erase (nextLeaf0 hn_s s) := by
            have h_eq := pruferDecodeAux_succ_step hn_s s 0 (by omega)
            dsimp at h_eq
            have h_min_eq := step_zero_min_eq_nextLeaf0 hm s
            rw [h_min_eq] at h_eq
            exact congrArg Prod.fst h_eq
          have h_subset := pruferDecodeAux_val_1_subset hn_s s (by omega) (by omega) (by omega : 1 ≤ m + 2 - 2)
          intro h_mem
          have h_mem_erase := h_subset h_mem
          rw [h_erase] at h_mem_erase
          simp only [Finset.mem_erase, ne_eq] at h_mem_erase
          exact h_mem_erase.1 trivial
        rintro rfl
        exact h_not_in_final hx
      have h_mem_compl : x ∈ ({nextLeaf0 hn_s s}ᶜ : Set (Fin (m + 2))) := h_not_nL
      let x_lift : {v // v ∈ ({nextLeaf0 hn_s s}ᶜ : Set (Fin (m + 2)))} := ⟨x, h_mem_compl⟩
      use (finSuccAboveEquivCompl (nextLeaf0 hn_s s)).symm x_lift
      constructor
      · have h_corr_v_spec := h_corr_v ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)).symm x_lift)
        have h_s_eq : (pruferDecodeAux hn_s s (m - 1 + 1) (by omega)).val.1 = (pruferFinalState hn_s s).1 := by
          have h_idx : m - 1 + 1 = m + 2 - 2 := by omega
          exact pruferDecodeAux_val_1_congr hn_s s (by omega) (by omega) h_idx
        rw [h_s_eq] at h_corr_v_spec
        apply h_corr_v_spec.mpr
        have h_eval : ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)).symm x_lift)).1 = x := by
          have h1 := Equiv.apply_symm_apply (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) x_lift
          rw [h1]
        rw [h_eval]
        exact hx
      · have h_eval : ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)).symm x_lift)).1 = x := by
          have h1 := Equiv.apply_symm_apply (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) x_lift
          rw [h1]
        exact h_eval

  have h_U_eq : ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastU hn_shift shift_s)).1 = pruferLastU hn_s s := by
    have h_min := min'_commutes_L (nextLeaf0 hn_s s) (pruferFinalState hn_shift shift_s).1 (pruferFinalState_nonempty hn_shift shift_s)
    have h_congr := min'_congr h_image_eq (Finset.Nonempty.image (pruferFinalState_nonempty hn_shift shift_s) _) (pruferFinalState_nonempty hn_s s)
    exact h_min.trans h_congr

  have h_erase_image : ((pruferFinalState hn_shift shift_s).1.erase (pruferLastU hn_shift shift_s)).image (fun v => ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) v).1) = (pruferFinalState hn_s s).1.erase (pruferLastU hn_s s) := by
    have h_im := h_image_eq
    ext x
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨v, ⟨hv_ne, hv_mem⟩, rfl⟩
      constructor
      · intro h_eq
        have h_eq_val : ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) v).1 = ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastU hn_shift shift_s)).1 := by
          rw [h_eq, h_U_eq]
        have h_inj := (finSuccAboveEquivCompl (nextLeaf0 hn_s s)).injective
        have h_eq_v := h_inj (Subtype.ext h_eq_val)
        exact hv_ne h_eq_v
      · rw [← h_im]
        simp only [Finset.mem_image]
        exact ⟨v, hv_mem, rfl⟩
    · rintro ⟨hx_ne, hx_mem⟩
      rw [← h_im] at hx_mem
      simp only [Finset.mem_image] at hx_mem
      rcases hx_mem with ⟨v, hv_mem, rfl⟩
      use v
      refine ⟨⟨?_, hv_mem⟩, rfl⟩
      intro h_eq_v
      rw [h_eq_v] at hx_ne
      exact hx_ne h_U_eq

  have h_V_eq : ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastV hn_shift shift_s)).1 = pruferLastV hn_s s := by
    have h_min := min'_commutes_L (nextLeaf0 hn_s s) ((pruferFinalState hn_shift shift_s).1.erase (pruferLastU hn_shift shift_s)) (pruferFinalErase_nonempty hn_shift shift_s)
    have h_congr := min'_congr h_erase_image (Finset.Nonempty.image (pruferFinalErase_nonempty hn_shift shift_s) _) (pruferFinalErase_nonempty hn_s s)
    exact h_min.trans h_congr

  have h_edges_corr : s(a, b) ∈ (pruferFinalState hn_shift shift_s).2 ↔ s(((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a).1, ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b).1) ∈ (pruferFinalState hn_s s).2 := by
    have h_corr_e_spec := h_corr_e a b
    have h_s_eq : (pruferDecodeAux hn_s s (m - 1 + 1) (by omega)).val.2 = (pruferFinalState hn_s s).2 := by
      have h_idx : m - 1 + 1 = m + 2 - 2 := by omega
      exact pruferDecodeAux_val_2_congr hn_s s (by omega) (by omega) h_idx
    rw [h_s_eq] at h_corr_e_spec
    exact h_corr_e_spec

  rw [deleteSmallestLeafTreeSucc_val_adj]
  dsimp [pruferDecode]
  simp only [SimpleGraph.fromEdgeSet_adj]

  change s(((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a).1, ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b).1) ∈ pruferDecodeEdges hn_s s ∧
    ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a).1 ≠ ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b).1 ↔
    s(a, b) ∈ pruferDecodeEdges hn_shift shift_s ∧ a ≠ b

  have h_ne_iff : (((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a).1 ≠ ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b).1) ↔ (a ≠ b) := by
    constructor
    · intro h h_eq
      rw [h_eq] at h
      exact h rfl
    · intro h h_eq
      have h_inj := (finSuccAboveEquivCompl (nextLeaf0 hn_s s)).injective
      have h_eq_v := Subtype.ext h_eq
      have h_eq_a := h_inj h_eq_v
      exact h h_eq_a

  rw [h_ne_iff]

  dsimp [pruferDecodeEdges]
  simp only [Finset.mem_insert]

  constructor
  · rintro ⟨(h_eq | h_mem), h_ne⟩
    · refine ⟨?_, h_ne⟩
      left
      simp only [Sym2.eq_iff] at h_eq ⊢
      rcases h_eq with (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left
        have h_ext_a : (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a = (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastU hn_shift shift_s) := Subtype.ext (by rw [h1, ← h_U_eq])
        have h_ext_b : (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b = (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastV hn_shift shift_s) := Subtype.ext (by rw [h2, ← h_V_eq])
        exact ⟨Equiv.injective _ h_ext_a, Equiv.injective _ h_ext_b⟩
      · right
        have h_ext_a : (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a = (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastV hn_shift shift_s) := Subtype.ext (by rw [h1, ← h_V_eq])
        have h_ext_b : (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b = (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastU hn_shift shift_s) := Subtype.ext (by rw [h2, ← h_U_eq])
        exact ⟨Equiv.injective _ h_ext_a, Equiv.injective _ h_ext_b⟩
    · refine ⟨?_, h_ne⟩
      right
      exact h_edges_corr.mpr h_mem
  · rintro ⟨(h_eq | h_mem), h_ne⟩
    · refine ⟨?_, h_ne⟩
      left
      simp only [Sym2.eq_iff] at h_eq ⊢
      rcases h_eq with (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left
        rw [h1, h2, h_U_eq, h_V_eq]
        exact ⟨rfl, rfl⟩
      · right
        rw [h1, h2, h_U_eq, h_V_eq]
        exact ⟨rfl, rfl⟩
    · refine ⟨?_, h_ne⟩
      right
      exact h_edges_corr.mp h_mem

lemma leftInverse_pruferDecode_aux
    (h_correspondence : ∀ (m' : ℕ) (hm' : 1 ≤ m') (s : pruferCodeSpace (m' + 2)),
       deleteSmallestLeafTreeSucc (m' + 1) (by omega) (pruferDecode (by omega) s) =
       pruferDecode (by omega : 2 ≤ m' + 1) (shiftedCode_v2 hm' s)) :
    ∀ (m : ℕ) (s : pruferCodeSpace (m + 2)), pruferEncodeAux m (pruferDecode (by omega) s) = s := by
  intro m
  induction m with
  | zero =>
    intro s
    ext i
    exact Fin.elim0 i
  | succ m ih =>
    intro s
    funext i
    by_cases h0 : i.val = 0
    · have hi : i = ⟨0, by omega⟩ := Fin.ext h0
      rw [hi]
      have h_zero := pruferEncode_pruferDecode_zero (m + 3) (by omega) s (by omega)
      exact h_zero
    · have hm1 : 1 ≤ m + 1 := by omega
      let leaf := smallestTreeLeaf (m + 3) (by omega) (pruferDecode (by omega) s)
      let T' := deleteSmallestLeafTreeSucc (m + 2) (by omega) (pruferDecode (by omega) s)
      have hT' : T' = pruferDecode (by omega) (shiftedCode_v2 hm1 s) := h_correspondence (m + 1) hm1 s

      have h_eval : (pruferEncodeAux (m + 1) (pruferDecode (by omega) s)) i =
          ((finSuccAboveEquivCompl leaf) (pruferEncodeAux m T' ⟨i.val - 1, by omega⟩)).1 := by
        dsimp [pruferEncodeAux]
        have h_pos : 0 < i.val := Nat.pos_of_ne_zero h0
        rw [dif_neg h0]

      rw [h_eval, hT']
      have h_ih := ih (shiftedCode_v2 hm1 s)
      have h_inner : pruferEncodeAux m (pruferDecode (by omega) (shiftedCode_v2 hm1 s)) ⟨i.val - 1, by omega⟩ =
          shiftedCode_v2 hm1 s ⟨i.val - 1, by omega⟩ := by
        rw [h_ih]
        rfl
      rw [h_inner]

      have h_leaf_eq : leaf = nextLeaf0 (by omega) s := rfl
      rw [h_leaf_eq]

      have h_i_pos : 1 ≤ i.val := Nat.pos_of_ne_zero h0
      have h_j_lt : i.val - 1 < m := by omega
      let j' : Fin m := ⟨i.val - 1, h_j_lt⟩
      let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)
      have h_shift_def : shiftedCode_v2 hm1 s j' =
          L.symm ⟨s i, nextLeaf0_not_in_image (by omega) s i⟩ := by
        dsimp [shiftedCode_v2]
        congr 1
        congr 1
        congr 1
        apply Fin.ext
        exact Nat.sub_add_cancel h_i_pos
      have h_L_app : (L (shiftedCode_v2 hm1 s j')).1 = s i := by
        rw [h_shift_def]
        simp only [Equiv.apply_symm_apply]
      exact h_L_app

-- Tier 1.5: take the structural correspondence as hypothesis.
theorem chapter31_tier2_of_correspondence {n : ℕ} (hn : 2 ≤ n)
    (h_correspondence : ∀ (m : ℕ) (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)),
       deleteSmallestLeafTreeSucc (m + 1) (by omega)
         (pruferDecode (by omega) s) =
       pruferDecode (by omega : 2 ≤ m + 1) (shiftedCode_v2 hm s)) :
    Fintype.card (LabeledTree n) = n ^ (n - 2) := by
  have h_left_inv : Function.LeftInverse (pruferEncode hn) (pruferDecode hn) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    intro s
    exact leftInverse_pruferDecode_aux h_correspondence m s
  have h_inj : Function.Injective (pruferDecode hn) := h_left_inv.injective
  -- cardinality of range = cardinality of domain
  have h_card_eq_ineq : Fintype.card (pruferCodeSpace n) ≤ Fintype.card (LabeledTree n) := Fintype.card_le_of_injective _ h_inj
  rw [pruferCodeSpace_card n] at h_card_eq_ineq
  have h_card_le := cayley_upper_bound n hn
  exact le_antisymm h_card_le h_card_eq_ineq




end ProofsInTheBook.Chapter31

open ProofsInTheBook.Chapter31
open SimpleGraph

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (LabeledTree n) = n ^ (n - 2) :=
  chapter31_tier2_of_correspondence hn
    (fun _ hm s => deleteSmallestLeaf_pruferDecode_v2 hm s)
