-- Prove2me | solution 1 for thomassen_conjecture_3connected
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T07:51:10.982827+00:00
-- url     : https://prove2.me/submissions/36027bb6-0d7e-4d8a-b8a8-75730e4151a3

import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Data.SetLike.Fintype
import Mathlib.Tactic.Ring

set_option Elab.async false


-- Compatibility lemmas backported with proof from Mathlib 0df444a
-- Paths.lean and CycleGraph.lean (Mathlib, Apache 2.0).
namespace SimpleGraph
namespace Walk
variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}
variable {u v : V} {f : G →g G'} {p : G.Walk u v}
alias ⟨_, IsPath.map⟩ := map_isPath_iff_of_injective

lemma isTrail_append {w : V} {p : G.Walk u v} {q : G.Walk v w} :
    (p.append q).IsTrail ↔ p.IsTrail ∧ q.IsTrail ∧ p.edges.Disjoint q.edges := by
  simp only [isTrail_def, edges_append, List.nodup_append']

theorem IsCycle.isPath_take {u n} {p : G.Walk u u} (h : p.IsCycle) (hn : n < p.length) :
    (p.take n).IsPath := by
  have hcyc : ((p.take n).append (p.drop n)).IsCycle := by
    simpa only [append_take_drop_eq] using h
  exact hcyc.isPath_of_append_left (by simpa only [nil_drop_iff] using (not_le.mpr hn))

theorem IsCycle.isPath_drop {u n} {p : G.Walk u u} (h : p.IsCycle) (hn : 0 < n) :
    (p.drop n).IsPath := by
  replace h : (p.drop 1).IsPath := h.isPath_tail
  exact h.drop_of_drop hn

theorem IsPath.length_eq_one_of_mem_edges {p : G.Walk u v} (hp : p.IsPath) (h : s(u, v) ∈ p.edges) :
    p.length = 1 := by
  suffices p.length - 1 = 0 by grind [length_edges]
  rw [← hp.getVert_eq_start_iff <| p.length.sub_le 1]
  exact (hp.eq_penultimate_of_mem_edges <| Sym2.eq_swap ▸ h).symm

theorem IsPath.eq_adj_toWalk_of_mem_edges {p : G.Walk u v} (hp : p.IsPath) (h : s(u, v) ∈ p.edges) :
    p = (p.adj_of_mem_edges h).toWalk := by
  apply p.ext_getVert_le_length <| by simp [hp.length_eq_one_of_mem_edges h]
  intro _ hl
  cases Nat.le_one_iff_eq_zero_or_eq_one.mp (hp.length_eq_one_of_mem_edges h ▸ hl) with
  | inl hl => simp [hl]
  | inr hl =>
    rw [hl, getVert_cons_succ, getVert_zero, ← hp.length_eq_one_of_mem_edges h, getVert_length]

theorem IsPath.disjoint_edges_of_disjoint_support {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath)
    (hd : p.support.tail.Disjoint q.support.tail) (hl : p.length ≠ 1) :
    p.edges.Disjoint q.edges := by
  simp only [List.disjoint_left] at hd ⊢
  contrapose! hd
  obtain ⟨⟨a, b⟩, hep, heq⟩ := hd
  have := p.mem_support_iff.mp <| p.fst_mem_support_of_mem_edges hep
  have := p.mem_support_iff.mp <| p.snd_mem_support_of_mem_edges hep
  have := q.mem_support_iff.mp <| q.fst_mem_support_of_mem_edges heq
  have := q.mem_support_iff.mp <| q.snd_mem_support_of_mem_edges heq
  grind [p.adj_of_mem_edges hep |>.ne, length_eq_one_of_mem_edges]

lemma IsPath.isCycle_append {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath) (hq : q.IsPath)
    (h : p.support.tail.Disjoint q.support.tail) (hn : 1 < p.length ∨ 1 < q.length) :
    (p.append q).IsCycle := by
  rw [isCycle_def, isTrail_append]
  refine ⟨⟨hp.isTrail, hq.isTrail, ?_⟩, ?_, ?_⟩
  · grind [IsPath.disjoint_edges_of_disjoint_support, List.Disjoint.symm]
  · intro hnil
    have hlen : p.length + q.length = 0 := by
      simpa only [length_append, length_nil] using congrArg Walk.length hnil
    omega
  · rw [tail_support_append, List.nodup_append']
    exact ⟨hp.support_nodup.tail, hq.support_nodup.tail, h⟩


end Walk
open Walk
section cycle

set_option backward.privateInPublic true in
private def cycleGraph.cycleCons (n : ℕ) : ∀ m : Fin (n + 3), (cycleGraph (n + 3)).Walk m 0
  | ⟨0, h⟩ => Walk.nil
  | ⟨m + 1, h⟩ =>
    have hadj : (cycleGraph (n + 3)).Adj ⟨m + 1, h⟩ ⟨m, Nat.lt_of_succ_lt h⟩ := by
      simp [cycleGraph_adj, Fin.ext_iff, Fin.sub_val_of_le]
    Walk.cons hadj (cycleGraph.cycleCons n ⟨m, Nat.lt_of_succ_lt h⟩)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The Eulerian cycle of `cycleGraph (n + 3)` -/
def cycleGraph.cycle (n : ℕ) : (cycleGraph (n + 3)).Walk 0 0 :=
  have hadj : (cycleGraph (n + 3)).Adj 0 (Fin.last (n + 2)) := by
    simp [cycleGraph_adj]
  Walk.cons hadj (cycleGraph.cycleCons n (Fin.last (n + 2)))


private theorem cycleGraph.length_cycle_cons (n : ℕ) :
    ∀ m : Fin (n + 3), (cycleGraph.cycleCons n m).length = m.val
  | ⟨0, h⟩ => by
    unfold cycleGraph.cycleCons
    rfl
  | ⟨m + 1, h⟩ => by
    unfold cycleGraph.cycleCons
    simp only [Walk.length_cons]
    rw [cycleGraph.length_cycle_cons n]

variable {n : ℕ}

@[simp, grind =]
theorem cycleGraph.length_cycle : (cycleGraph.cycle n).length = n + 3 := by
  unfold cycleGraph.cycle
  simp [cycleGraph.length_cycle_cons]


private theorem cycleGraph.getVert_cycleCons (m : Fin (n + 3)) (i : ℕ) (hi : i ≤ m.val) :
    (cycleGraph.cycleCons n m).getVert i = (m - i) % (n + 3) := by
  obtain ⟨m, hm⟩ := m
  induction i generalizing m
  · simp [Nat.mod_eq_of_lt hm]
  · cases m <;> grind +locals [getVert_cons_succ]

theorem cycleGraph.getVert_cycle {m : ℕ} (hm : m ≤ n + 3) :
    (cycleGraph.cycle n).getVert m = ⟨(n + 3 - m) % (n + 3), Nat.mod_lt _ (by lia)⟩ := by
  cases m
  · simp
  · grind +locals [getVert_cons_succ, cycleGraph.getVert_cycleCons]

theorem cycleGraph.isPath_tail_cycle : (cycleGraph.cycle n).tail.IsPath := by
  refine isPath_iff_injective_get_support _ |>.mpr fun ⟨i, hi⟩ ⟨j, hj⟩ hij ↦ ?_
  rw [support_tail_of_not_nil _ (of_decide_eq_false rfl)] at hi hj
  simp only [List.get_eq_getElem, support_getElem_eq_getVert, getVert_tail] at hij
  grind [← Nat.mod_eq_of_lt, cycleGraph.getVert_cycle]

theorem cycleGraph.isCycle_cycle : (cycleGraph.cycle n).IsCycle :=
  isCycle_iff_isPath_tail_and_le_length.mpr ⟨cycleGraph.isPath_tail_cycle, by simp⟩

end cycle

section IsContained

variable {V : Type*} {G : SimpleGraph V}

lemma cycleGraph_isContained_iff {n : ℕ} (hn : 2 < n) :
    cycleGraph n ⊑ G ↔ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n := by
  refine ⟨fun ⟨h⟩ ↦ ?_, fun h' ↦ ?_⟩
  · have : n = n - 3 + 3 := by lia
    rw [this] at h
    refine ⟨h.toHom ⟨0, by lia⟩, Walk.map h.toHom <| cycleGraph.cycle (n - 3), ?_, ?_⟩
    · exact (map_isCycle_iff_of_injective h.injective).mpr cycleGraph.isCycle_cycle
    · simp [cycleGraph.length_cycle, ← this]
  · obtain ⟨a, p, hp₁, hp₂⟩ := h'
    refine ⟨⟨⟨fun n ↦ p.support[n.succ]'(?_), ?_⟩, ?_⟩⟩
    · grind [hp₁.three_le_length, length_tail_add_one, not_nil_iff_lt_length]
    · intro ⟨x, hx⟩ ⟨y, hy⟩ hab
      have hne : x ≠ y := fun _ ↦ by simp_all
      wlog hle : x > y
      · exact this hn a p hp₁ hp₂ y hy x hx hab.symm hne.symm (by lia) |>.symm
      rcases cycleGraph_adj'.mp hab with hab | hab
      · simp_rw [show x = y + 1 by grind [Fin.sub_val_of_le]]
        exact p.isChain_adj_support.getElem _ _ |>.symm
      · rw [Fin.coe_sub_iff_lt.mpr hle] at hab
        simp_rw [show x = n - 1 by lia, show y = 0 by lia, Fin.succ_mk, show n - 1 + 1 = n by lia]
        simp [← hp₂, p.adj_snd hp₁.not_nil]
    · have hlen : p.tail.support.length = n := by
        grind [length_tail_add_one, not_nil_iff_lt_length]
      have (m : Fin n) : p.support[m.succ]'(by grind) = p.tail.support[m] := by
        simp [p.support_tail_of_not_nil hp₁.not_nil]
      simp_rw [this]
      have := IsPath.mk' <| (support_tail_of_not_nil _ hp₁.not_nil) ▸ hp₁.support_nodup
      exact hlen ▸ (isPath_iff_injective_get_support _ |>.mp this)

end IsContained


end SimpleGraph

/- Complete module MengerData; source SHA256 18016818c4a35cba44b617ac694b034bcdcfc68c130a6e573aebfc7bc00de53a. -/
section DiracBundledModule0000

namespace FiniteVertexMenger

variable {V : Type*} [DecidableEq V]

def Avoids {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (S : Finset V) : Prop :=
  ∀ v, v ∈ p.support → v ∉ S

def Separates (G : SimpleGraph V) (A B S : Finset V) : Prop :=
  ∀ a, a ∈ A → ∀ b, b ∈ B →
    ∀ p : G.Walk a b, ∃ v, v ∈ p.support ∧ v ∈ S

def NoSmallSeparator (G : SimpleGraph V) (A B : Finset V) (k : Nat) : Prop :=
  ∀ S : Finset V, Separates G A B S → k ≤ S.card

structure DisjointPaths (G : SimpleGraph V) (A B : Finset V) (k : Nat) where
  start : Fin k → V
  finish : Fin k → V
  start_mem : ∀ i, start i ∈ A
  finish_mem : ∀ i, finish i ∈ B
  path : ∀ i, G.Walk (start i) (finish i)
  isPath : ∀ i, (path i).IsPath
  disjoint : Pairwise (fun i j =>
    Disjoint (path i).support.toFinset (path j).support.toFinset)

def CleanTo {G : SimpleGraph V} {A T : Finset V} {k : Nat}
    (F : DisjointPaths G A T k) : Prop :=
  ∀ i v, v ∈ (F.path i).support → v ∈ T → v = F.finish i

def CleanFrom {G : SimpleGraph V} {T B : Finset V} {k : Nat}
    (F : DisjointPaths G T B k) : Prop :=
  ∀ i v, v ∈ (F.path i).support → v ∈ T → v = F.start i

structure Fan (G : SimpleGraph V) (x : V) (T : Finset V) (r : Nat) where
  root_not_mem : x ∉ T
  tip : Fin r → V
  tip_mem : ∀ i, tip i ∈ T
  tip_injective : Function.Injective tip
  arm : ∀ i, G.Walk x (tip i)
  isPath : ∀ i, (arm i).IsPath
  first_contact : ∀ i v, v ∈ (arm i).support → v ∈ T → v = tip i
  disjoint_tail : Pairwise (fun i j =>
    Disjoint (arm i).support.tail.toFinset (arm j).support.tail.toFinset)

end FiniteVertexMenger
end DiracBundledModule0000

/- Complete module MengerBasics; source SHA256 e417576582cb98f0f3f935ae0ad1f34c872a42484b40ef8428faff19a7321966. -/
section DiracBundledModule0001

namespace FiniteVertexMenger

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem Separates.of_left (G : SimpleGraph V) (A B : Finset V) :
    Separates G A B A := by
  intro a ha b _ p
  exact ⟨a, p.start_mem_support, ha⟩

omit [DecidableEq V] in
theorem Separates.of_right (G : SimpleGraph V) (A B : Finset V) :
    Separates G A B B := by
  intro a _ b hb p
  exact ⟨b, p.end_mem_support, hb⟩

omit [DecidableEq V] in
theorem NoSmallSeparator.le_card_left {G : SimpleGraph V} {A B : Finset V} {k : Nat}
    (h : NoSmallSeparator G A B k) : k ≤ A.card :=
  h A (Separates.of_left G A B)

omit [DecidableEq V] in
theorem NoSmallSeparator.le_card_right {G : SimpleGraph V} {A B : Finset V} {k : Nat}
    (h : NoSmallSeparator G A B k) : k ≤ B.card :=
  h B (Separates.of_right G A B)

theorem exists_disjointPaths_zero (G : SimpleGraph V) (A B : Finset V) :
    Nonempty (DisjointPaths G A B 0) := by
  exact ⟨{
    start := fun i => i.elim0
    finish := fun i => i.elim0
    start_mem := fun i => i.elim0
    finish_mem := fun i => i.elim0
    path := fun i => i.elim0
    isPath := fun i => i.elim0
    disjoint := fun i => i.elim0
  }⟩

theorem exists_disjointPaths_of_common (G : SimpleGraph V) (A B : Finset V)
    (k : Nat) (hcommon : k ≤ (A ∩ B).card) :
    Nonempty (DisjointPaths G A B k) := by
  classical
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hcommon
  have htype : Fintype.card T = k := by simpa only [Fintype.card_coe] using hcard
  let e : Fin k ≃ T := (Fintype.equivFinOfCardEq htype).symm
  refine ⟨{
    start := fun i => (e i).val
    finish := fun i => (e i).val
    start_mem := fun i => (Finset.mem_inter.mp (hT (e i).property)).1
    finish_mem := fun i => (Finset.mem_inter.mp (hT (e i).property)).2
    path := fun _ => SimpleGraph.Walk.nil
    isPath := fun _ => SimpleGraph.Walk.IsPath.nil
    disjoint := ?_
  }⟩
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro v hi hj
  have hvi : v = (e i).val := by simpa using hi
  have hvj : v = (e j).val := by simpa using hj
  exact hij (e.injective (Subtype.ext (hvi.symm.trans hvj)))

theorem separates_bot_inter (A B : Finset V) :
    Separates (⊥ : SimpleGraph V) A B (A ∩ B) := by
  intro a ha b hb p
  cases p with
  | nil => exact ⟨_, by simp, Finset.mem_inter.mpr ⟨ha, hb⟩⟩
  | cons h p => simp at h

theorem exists_disjointPaths_bot (A B : Finset V) (k : Nat)
    (h : NoSmallSeparator (⊥ : SimpleGraph V) A B k) :
    Nonempty (DisjointPaths (⊥ : SimpleGraph V) A B k) :=
  exists_disjointPaths_of_common _ A B k (h (A ∩ B) (separates_bot_inter A B))

end FiniteVertexMenger
end DiracBundledModule0001

/- Complete module PathFamilyOperations; source SHA256 ce00c4763c9f3f4061994be063660cd81383efec37776f234fd3db3cc35f65cd. -/
section DiracBundledModule0002

namespace FiniteVertexMenger

variable {V : Type*} [DecidableEq V]

theorem firstHit {G : SimpleGraph V} {a b : V} {T : Finset V}
    {p : G.Walk a b} (hp : p.IsPath) (hb : b ∈ T) :
    ∃ c, c ∈ T ∧ ∃ q : G.Walk a c,
      q.IsPath ∧ q.support ⊆ p.support ∧
      (∀ v, v ∈ q.support → v ∈ T → v = c) := by
  induction p with
  | nil =>
      exact ⟨_, hb, .nil, .nil, by simp, by simp⟩
  | @cons a v b hav p ih =>
      by_cases ha : a ∈ T
      · refine ⟨a, ha, .nil, .nil, ?_, ?_⟩ <;> simp
      · obtain ⟨c, hc, q, hq, hsub, hclean⟩ := ih hp.of_cons hb
        refine ⟨c, hc, .cons hav q, hq.cons ?_, ?_, ?_⟩
        · exact fun h => (SimpleGraph.Walk.cons_isPath_iff hav p).mp hp |>.2 (hsub h)
        · simpa only [SimpleGraph.Walk.support_cons] using List.cons_subset_cons a hsub
        · intro w hw hwT
          rcases List.mem_cons.mp hw with rfl | hw
          · exact (ha hwT).elim
          · exact hclean w hw hwT

namespace DisjointPaths

variable {G H : SimpleGraph V} {A B : Finset V} {k : ℕ}

def reverse (F : DisjointPaths G A B k) : DisjointPaths G B A k where
  start := F.finish
  finish := F.start
  start_mem := F.finish_mem
  finish_mem := F.start_mem
  path i := (F.path i).reverse
  isPath i := (F.isPath i).reverse
  disjoint i j hij := by
    simpa only [SimpleGraph.Walk.support_reverse, List.toFinset_reverse] using F.disjoint hij

theorem start_injective (F : DisjointPaths G A B k) : Function.Injective F.start := by
  intro i j h
  by_contra hij
  apply Finset.disjoint_left.mp (F.disjoint hij)
    (show F.start i ∈ (F.path i).support.toFinset by simp)
  simpa only [h, List.mem_toFinset] using (F.path j).start_mem_support

theorem finish_injective (F : DisjointPaths G A B k) : Function.Injective F.finish := by
  exact F.reverse.start_injective

theorem start_bijective (F : DisjointPaths G A B k) (hcard : A.card = k) :
    Function.Bijective (fun i : Fin k => (⟨F.start i, F.start_mem i⟩ : A)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨fun i j h => F.start_injective (congrArg Subtype.val h), ?_⟩
  simpa using hcard.symm

theorem finish_bijective (F : DisjointPaths G A B k) (hcard : B.card = k) :
    Function.Bijective (fun i : Fin k => (⟨F.finish i, F.finish_mem i⟩ : B)) := by
  exact F.reverse.start_bijective hcard

def mono (F : DisjointPaths G A B k) (hGH : G ≤ H) : DisjointPaths H A B k where
  start := F.start
  finish := F.finish
  start_mem := F.start_mem
  finish_mem := F.finish_mem
  path i := (F.path i).mapLe hGH
  isPath i := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_mapLe_eq_support]
    exact (F.isPath i).support_nodup
  disjoint i j hij := by
    simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using F.disjoint hij

end DisjointPaths

theorem familyCleanTo {G : SimpleGraph V} {A T : Finset V} {k : ℕ}
    (F : DisjointPaths G A T k) :
    ∃ F' : DisjointPaths G A T k, CleanTo F' ∧ F'.start = F.start ∧
      ∀ i, (F'.path i).support ⊆ (F.path i).support := by
  classical
  choose c hc q hq hsub hclean using fun i => firstHit (F.isPath i) (F.finish_mem i)
  let F' : DisjointPaths G A T k := {
    start := F.start
    finish := c
    start_mem := F.start_mem
    finish_mem := hc
    path := q
    isPath := hq
    disjoint := by
      intro i j hij
      apply (F.disjoint hij).mono
      · intro v hv
        exact List.mem_toFinset.mpr (hsub i (List.mem_toFinset.mp hv))
      · intro v hv
        exact List.mem_toFinset.mpr (hsub j (List.mem_toFinset.mp hv))
  }
  exact ⟨F', hclean, rfl, hsub⟩

theorem familyCleanFrom {G : SimpleGraph V} {T B : Finset V} {k : ℕ}
    (F : DisjointPaths G T B k) :
    ∃ F' : DisjointPaths G T B k, CleanFrom F' ∧ F'.finish = F.finish ∧
      ∀ i, (F'.path i).support ⊆ (F.path i).support := by
  obtain ⟨R, hR, hstart, hsub⟩ := familyCleanTo F.reverse
  refine ⟨R.reverse, ?_, hstart, ?_⟩
  · intro i v hv hvT
    exact hR i v (by simpa only [DisjointPaths.reverse, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] using hv) hvT
  · intro i v hv
    have h := hsub i (by simpa only [DisjointPaths.reverse,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] using hv)
    simpa only [DisjointPaths.reverse, SimpleGraph.Walk.support_reverse, List.mem_reverse] using h

theorem glue_families {G H : SimpleGraph V} {A B S : Finset V}
    {x y : V} {k : ℕ} (hHG : H ≤ G) (_hxy : x ≠ y)
    (hx : x ∉ S) (hy : y ∉ S) (hcard : S.card + 1 = k)
    (L : DisjointPaths H A (insert x S) k)
    (R : DisjointPaths H (insert y S) B k)
    (hedge : G.Adj x y)
    (hcross : ∀ i j v, v ∈ (L.path i).support → v ∈ (R.path j).support →
      v = L.finish i ∧ v = R.start j ∧ v ∈ S) :
    Nonempty (DisjointPaths G A B k) := by
  classical
  have hfix : ∀ v ∈ S, Equiv.swap x y v = v := by
    intro v hv
    exact Equiv.swap_apply_of_ne_of_ne
      (fun h => hx (h ▸ hv)) (fun h => hy (h ▸ hv))
  have hright : (insert y S).card = k := by
    simpa only [Finset.card_insert_of_notMem hy] using hcard
  have hmatch_exists : ∀ i, ∃ j, R.start j = Equiv.swap x y (L.finish i) := by
    intro i
    have hmem : Equiv.swap x y (L.finish i) ∈ insert y S := by
      rcases Finset.mem_insert.mp (L.finish_mem i) with h | h
      · simp only [h, Equiv.swap_apply_left, Finset.mem_insert_self]
      · rw [hfix _ h]
        exact Finset.mem_insert_of_mem h
    obtain ⟨j, hj⟩ := (R.start_bijective hright).surjective ⟨_, hmem⟩
    exact ⟨j, congrArg Subtype.val hj⟩
  choose σ hσ using hmatch_exists
  have hσinj : Function.Injective σ := by
    intro i j hij
    apply L.finish_injective
    apply (Equiv.swap x y).injective
    rw [← hσ i, ← hσ j, hij]
  have hsame : ∀ i, L.finish i ∈ S → R.start (σ i) = L.finish i := by
    intro i hi
    rw [hσ, hfix _ hi]
  have hcross_index : ∀ i j v, v ∈ (L.path i).support →
      v ∈ (R.path (σ j)).support → i = j := by
    intro i j v hi hj
    obtain ⟨hvL, hvR, hvS⟩ := hcross i (σ j) v hi hj
    apply hσinj
    apply R.start_injective
    exact (hsame i (hvL ▸ hvS)).trans (hvL.symm.trans hvR)
  -- Match the shared cut endpoints, and join the unique unmatched pair across xy.
  have hwalk : ∀ i, ∃ q : G.Walk (L.start i) (R.finish (σ i)),
      ∀ v, v ∈ q.support →
        v ∈ (L.path i).support ∨ v ∈ (R.path (σ i)).support := by
    intro i
    by_cases hi : L.finish i = x
    · have hstart : R.start (σ i) = y := by
        rw [hσ, hi, Equiv.swap_apply_left]
      refine ⟨((((L.path i).mapLe hHG).copy rfl hi).concat hedge).append
        (((R.path (σ i)).mapLe hHG).copy hstart rfl), ?_⟩
      intro v hv
      simp only [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_concat, List.concat_eq_append, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_mapLe_eq_support, List.mem_append,
        List.mem_singleton] at hv
      rcases hv with (hv | rfl) | hv
      · exact Or.inl hv
      · exact Or.inr (by simpa only [hstart] using (R.path (σ i)).start_mem_support)
      · exact Or.inr hv
    · have hstart := hsame i ((Finset.mem_insert.mp (L.finish_mem i)).resolve_left hi)
      refine ⟨((L.path i).mapLe hHG).append
        (((R.path (σ i)).mapLe hHG).copy hstart rfl), ?_⟩
      intro v hv
      simpa only [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_mapLe_eq_support] using hv
  choose q hq using hwalk
  -- Bypassing repeated vertices cannot introduce any new intersections.
  refine ⟨{
    start := L.start
    finish := fun i => R.finish (σ i)
    start_mem := L.start_mem
    finish_mem := fun i => R.finish_mem (σ i)
    path := fun i => (q i).bypass
    isPath := fun i => (q i).bypass_isPath
    disjoint := ?_
  }⟩
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  have hi := hq i v ((q i).support_bypass_subset (List.mem_toFinset.mp hvi))
  have hj := hq j v ((q j).support_bypass_subset (List.mem_toFinset.mp hvj))
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact Finset.disjoint_left.mp (L.disjoint hij)
      (List.mem_toFinset.mpr hi) (List.mem_toFinset.mpr hj)
  · exact hij (hcross_index i j v hi hj)
  · exact hij (hcross_index j i v hj hi).symm
  · exact Finset.disjoint_left.mp (R.disjoint (hσinj.ne hij))
      (List.mem_toFinset.mpr hi) (List.mem_toFinset.mpr hj)

end FiniteVertexMenger
end DiracBundledModule0002

/- Complete module SeparatorDeletion; source SHA256 bc28a41b859b32fef6c1d8426e1ca93122b1bd5ebe47ca3236e70f07477f863b. -/
section DiracBundledModule0003

namespace FiniteVertexMenger

open SimpleGraph

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem separates_iff_no_avoiding_walk {G : SimpleGraph V} {A B S : Finset V} :
    Separates G A B S ↔
      ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b, ¬ Avoids p S := by
  classical
  simp only [Separates, Avoids, not_forall, not_not, exists_prop]

omit [DecidableEq V] in
theorem separates_iff_not_reachable_induce {G : SimpleGraph V} {A B S : Finset V} :
    Separates G A B S ↔
      ∀ a ∈ A, ∀ b ∈ B, ∀ ha : a ∉ S, ∀ hb : b ∉ S,
        ¬ (G.induce (S : Set V)ᶜ).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  classical
  rw [separates_iff_no_avoiding_walk]
  constructor
  · intro h a ha b hb haS hbS hr
    obtain ⟨p⟩ := hr
    have hp : Avoids (p.map (Embedding.induce (S : Set V)ᶜ).toHom) S := by
      intro v hv
      rw [Walk.support_map] at hv
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv
      exact w.property
    exact h a ha b hb _ hp
  · intro h a ha b hb p hp
    apply h a ha b hb (hp a p.start_mem_support) (hp b p.end_mem_support)
    exact ⟨p.induce (S : Set V)ᶜ hp⟩

noncomputable def reachableRegion [Fintype V] (G : SimpleGraph V)
    (A S : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ∃ a ∈ A, ∃ p : G.Walk a v, Avoids p S

omit [DecidableEq V] in
@[simp] theorem mem_reachableRegion [Fintype V] {G : SimpleGraph V}
    {A S : Finset V} {v : V} :
    v ∈ reachableRegion G A S ↔ ∃ a ∈ A, ∃ p : G.Walk a v, Avoids p S := by
  classical
  simp [reachableRegion]

omit [DecidableEq V] in
theorem reachableRegion_disjoint [Fintype V] (G : SimpleGraph V) (A S : Finset V) :
    Disjoint (reachableRegion G A S) S := by
  apply Finset.disjoint_left.mpr
  intro v hv hvS
  obtain ⟨a, _, p, hp⟩ := mem_reachableRegion.mp hv
  exact hp v p.end_mem_support hvS

omit [DecidableEq V] in
theorem start_mem_reachableRegion [Fintype V] {G : SimpleGraph V}
    {A S : Finset V} {a : V} (ha : a ∈ A) (haS : a ∉ S) :
    a ∈ reachableRegion G A S := by
  apply mem_reachableRegion.mpr
  refine ⟨a, ha, .nil, ?_⟩
  simpa only [Avoids, Walk.support_nil, List.mem_singleton, forall_eq] using haS

omit [DecidableEq V] in
theorem finish_not_mem_reachableRegion [Fintype V] {G : SimpleGraph V}
    {A B S : Finset V} (hsep : Separates G A B S) {b : V} (hb : b ∈ B) :
    b ∉ reachableRegion G A S := by
  intro hr
  obtain ⟨a, ha, p, hp⟩ := mem_reachableRegion.mp hr
  exact (separates_iff_no_avoiding_walk.mp hsep) a ha b hb p hp

omit [DecidableEq V] in
theorem reachableRegion_adj [Fintype V] {G : SimpleGraph V} {A S : Finset V}
    {u v : V} (hu : u ∈ reachableRegion G A S) (hvS : v ∉ S) (h : G.Adj u v) :
    v ∈ reachableRegion G A S := by
  obtain ⟨a, ha, p, hp⟩ := mem_reachableRegion.mp hu
  apply mem_reachableRegion.mpr
  refine ⟨a, ha, p.concat h, ?_⟩
  intro w hw
  rw [Walk.support_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact hp w hw
  · exact hvS

omit [DecidableEq V] in
theorem reachableRegion_no_cross [Fintype V] {G : SimpleGraph V} {A S : Finset V}
    {u v : V} (hu : u ∈ reachableRegion G A S) (hv : v ∉ reachableRegion G A S)
    (hvS : v ∉ S) : ¬ G.Adj u v := by
  exact fun h => hv (reachableRegion_adj hu hvS h)

theorem walk_prefix_to_boundary {G H : SimpleGraph V} {U T : Finset V}
    (hstep : ∀ u ∈ U, u ∉ T → ∀ v, G.Adj u v → H.Adj u v ∧ (v ∈ T ∨ v ∈ U))
    {a b : V} (p : G.Walk a b) (ha : a ∈ U ∨ a ∈ T) (hb : b ∉ U ∨ b ∈ T) :
    ∃ c ∈ T, ∃ q : H.Walk a c, q.support ⊆ p.support := by
  classical
  induction p with
  | @nil a =>
      have hat : a ∈ T := by tauto
      exact ⟨a, hat, .nil, fun _ h => h⟩
  | @cons a v b h p ih =>
      by_cases hat : a ∈ T
      · refine ⟨a, hat, .nil, ?_⟩
        simp
      · have hau : a ∈ U := ha.resolve_right hat
        obtain ⟨hh, hv⟩ := hstep a hau hat v h
        obtain ⟨c, hc, q, hq⟩ := ih hv.symm hb
        refine ⟨c, hc, .cons hh q, ?_⟩
        intro w hw
        simp only [Walk.support_cons, List.mem_cons] at hw ⊢
        exact hw.imp_right (hq ·)

theorem walk_cross_boundary {G : SimpleGraph V} {U : Finset V}
    {a b : V} (p : G.Walk a b) (ha : a ∈ U) (hb : b ∉ U) :
    ∃ x y, x ∈ p.support ∧ y ∈ p.support ∧ G.Adj x y ∧ x ∈ U ∧ y ∉ U := by
  induction p with
  | nil => exact (hb ha).elim
  | @cons a v b h p ih =>
      by_cases hv : v ∈ U
      · obtain ⟨x, y, hx, hy, hxy, hxU, hyU⟩ := ih hv hb
        exact ⟨x, y, List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy, hxy, hxU, hyU⟩
      · exact ⟨a, v, by simp, by simp, h, ha, hv⟩

theorem deleted_edge_prefix {G : SimpleGraph V} {e : Sym2 V} {x y : V}
    (he : e = s(x, y)) {U S : Finset V} (hy : y ∉ U)
    (hclosed : ∀ u ∈ U, u ∉ S → ∀ v, v ∉ S →
      (G.deleteEdges {e}).Adj u v → v ∈ U)
    {a b : V} (p : G.Walk a b) (ha : a ∈ U ∨ a ∈ S) (hb : b ∉ U ∨ b ∈ S) :
    ∃ c ∈ insert x S, ∃ q : (G.deleteEdges {e}).Walk a c,
      q.support ⊆ p.support := by
  apply walk_prefix_to_boundary (U := U) (T := insert x S) ?_ p
    (ha.imp_right Finset.mem_insert_of_mem) (hb.imp_right Finset.mem_insert_of_mem)
  intro u hu huT v huv
  have hux : u ≠ x := by intro h; subst u; exact huT (Finset.mem_insert_self _ _)
  have huy : u ≠ y := by intro h; subst u; exact hy hu
  have huS : u ∉ S := fun h => huT (Finset.mem_insert_of_mem h)
  have hh : (G.deleteEdges {e}).Adj u v := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨huv, ?_⟩
    simp only [Set.mem_singleton_iff, he, Sym2.eq_iff]
    tauto
  refine ⟨hh, ?_⟩
  by_cases hvS : v ∈ S
  · exact Or.inl (Finset.mem_insert_of_mem hvS)
  · exact Or.inr (hclosed u hu huS v hvS hh)

structure EssentialEdgeStep (G : SimpleGraph V) (A B : Finset V)
    (k : Nat) (e : Sym2 V) where
  left : V
  right : V
  cut : Finset V
  region : Finset V
  edge_eq : e = s(left, right)
  adjacent : G.Adj left right
  left_not_mem : left ∉ cut
  right_not_mem : right ∉ cut
  card_cut : cut.card + 1 = k
  separates : Separates (G.deleteEdges {e}) A B cut
  region_disjoint : Disjoint region cut
  left_mem : left ∈ region
  right_not_mem_region : right ∉ region
  starts_in_region : ∀ a, a ∈ A → a ∉ cut → a ∈ region
  finishes_outside : ∀ b, b ∈ B → b ∉ cut → b ∉ region
  no_cross : ∀ u v, u ∈ region → v ∉ region → v ∉ cut →
    ¬ (G.deleteEdges {e}).Adj u v
  left_problem : NoSmallSeparator (G.deleteEdges {e}) A (insert left cut) k
  right_problem : NoSmallSeparator (G.deleteEdges {e}) (insert right cut) B k

theorem essential_edge_step [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (k : Nat) (e : Sym2 V)
    (_hk : 0 < k) (hG : NoSmallSeparator G A B k)
    (_he : e ∈ G.edgeFinset)
    (hH : ¬ NoSmallSeparator (G.deleteEdges {e}) A B k) :
    Nonempty (EssentialEdgeStep G A B k e) := by
  classical
  let H := G.deleteEdges {e}
  obtain ⟨S, hS, hlt⟩ : ∃ S : Finset V, Separates H A B S ∧ S.card < k := by
    simpa only [NoSmallSeparator, not_forall, not_le, exists_prop] using hH
  have hnot : ¬ Separates G A B S := fun h => Nat.not_le_of_lt hlt (hG S h)
  unfold Separates at hnot
  push Not at hnot
  obtain ⟨a, ha, b, hb, p, hp⟩ := hnot
  change Avoids p S at hp
  let U := reachableRegion H A S
  have haU : a ∈ U := start_mem_reachableRegion ha (hp a p.start_mem_support)
  have hbU : b ∉ U := finish_not_mem_reachableRegion hS hb
  obtain ⟨x, y, hxp, hyp, hxy, hxU, hyU⟩ := walk_cross_boundary p haU hbU
  have hxS : x ∉ S := hp x hxp
  have hyS : y ∉ S := hp y hyp
  have hnH : ¬ H.Adj x y := reachableRegion_no_cross hxU hyU hyS
  have heq : e = s(x, y) := by
    by_contra hne
    apply hnH
    exact SimpleGraph.deleteEdges_adj.mpr ⟨hxy, by
      simpa only [Set.mem_singleton_iff] using Ne.symm hne⟩
  have hclosed : ∀ u ∈ U, u ∉ S → ∀ v, v ∉ S → H.Adj u v → v ∈ U := by
    intro u hu _ v hv huv
    exact reachableRegion_adj hu hv huv
  have hprefix : ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b,
      ∃ c ∈ insert x S, ∃ q : H.Walk a c, q.support ⊆ p.support := by
    intro a ha b hb p
    apply deleted_edge_prefix heq hyU hclosed p
    · by_cases haS : a ∈ S
      · exact Or.inr haS
      · exact Or.inl (start_mem_reachableRegion ha haS)
    · exact Or.inl (finish_not_mem_reachableRegion hS hb)
  have hsepX : Separates G A B (insert x S) := by
    intro a ha b hb p
    obtain ⟨c, hc, q, hq⟩ := hprefix a ha b hb p
    exact ⟨c, hq q.end_mem_support, hc⟩
  have hcard : S.card + 1 = k := by
    have hle := hG (insert x S) hsepX
    rw [Finset.card_insert_of_notMem hxS] at hle
    omega
  have hleft : NoSmallSeparator H A (insert x S) k := by
    intro T hT
    apply hG T
    intro a ha b hb p
    obtain ⟨c, hc, q, hq⟩ := hprefix a ha b hb p
    obtain ⟨v, hvq, hvT⟩ := hT a ha c hc q
    exact ⟨v, hq hvq, hvT⟩
  let W := Finset.univ \ U
  have hxW : x ∉ W := by simp [W, hxU]
  have hclosedW : ∀ u ∈ W, u ∉ S → ∀ v, v ∉ S → H.Adj u v → v ∈ W := by
    intro u hu huS v hvS huv
    have huU : u ∉ U := (Finset.mem_sdiff.mp hu).2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hvU
    exact huU (hclosed v hvU hvS u huS huv.symm)
  have hright : NoSmallSeparator H (insert y S) B k := by
    intro T hT
    apply hG T
    intro a ha b hb p
    have hbW : b ∈ W := by
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, finish_not_mem_reachableRegion hS hb⟩
    have haW : a ∉ W ∨ a ∈ S := by
      by_cases haS : a ∈ S
      · exact Or.inr haS
      · exact Or.inl fun h => (Finset.mem_sdiff.mp h).2
          (start_mem_reachableRegion ha haS)
    obtain ⟨c, hc, q, hq⟩ := deleted_edge_prefix (heq.trans (Sym2.eq_swap))
      hxW hclosedW p.reverse (Or.inl hbW) haW
    obtain ⟨v, hvq, hvT⟩ := hT c hc b hb q.reverse
    have hv : v ∈ p.reverse.support := hq (by simpa using hvq)
    exact ⟨v, by simpa using hv, hvT⟩
  exact ⟨{
    left := x, right := y, cut := S, region := U
    edge_eq := heq, adjacent := hxy
    left_not_mem := hxS, right_not_mem := hyS, card_cut := hcard
    separates := hS, region_disjoint := reachableRegion_disjoint H A S
    left_mem := hxU, right_not_mem_region := hyU
    starts_in_region := fun _ ha haS => start_mem_reachableRegion ha haS
    finishes_outside := fun _ hb _ => finish_not_mem_reachableRegion hS hb
    no_cross := fun _ _ hu hv hvS => reachableRegion_no_cross hu hv hvS
    left_problem := hleft, right_problem := hright }⟩

theorem clean_prefix_avoids {G : SimpleGraph V} {S : Finset V} {a b v : V}
    {p : G.Walk a b} (hp : p.IsPath)
    (hclean : ∀ w ∈ p.support, w ∈ S → w = b)
    (hv : v ∈ p.support) (hvS : v ∉ S) : Avoids (p.takeUntil v hv) S := by
  intro w hw hwS
  have hwb : w = b := hclean w (p.support_takeUntil_subset hv hw) hwS
  have hbS : b ∈ S := hwb ▸ hwS
  have hbv : b ≠ v := fun h => hvS (h ▸ hbS)
  apply Walk.endpoint_notMem_support_takeUntil hp hv hbv
  simpa only [hwb] using hw

omit [DecidableEq V] in
theorem avoiding_endpoint_in_region {G : SimpleGraph V} {S U : Finset V}
    (hclosed : ∀ u ∈ U, ∀ v, v ∉ S → G.Adj u v → v ∈ U)
    {a b : V} (p : G.Walk a b) (hp : Avoids p S) (ha : a ∈ U) : b ∈ U := by
  induction p with
  | nil => exact ha
  | @cons a v b h p ih =>
      apply ih
      · intro w hw
        exact hp w (List.mem_cons_of_mem _ hw)
      · exact hclosed a ha v (hp v (by simp)) h

namespace EssentialEdgeStep

variable {G : SimpleGraph V} {A B : Finset V} {k : Nat} {e : Sym2 V}

theorem left_support (E : EssentialEdgeStep G A B k e)
    (L : DisjointPaths (G.deleteEdges {e}) A (insert E.left E.cut) k)
    (hL : CleanTo L) {i : Fin k} {v : V}
    (hv : v ∈ (L.path i).support) (hvS : v ∉ E.cut) : v ∈ E.region := by
  let q := (L.path i).takeUntil v hv
  have hq : Avoids q E.cut := clean_prefix_avoids (L.isPath i)
    (fun w hw hwS => hL i w hw (Finset.mem_insert_of_mem hwS)) hv hvS
  apply avoiding_endpoint_in_region (S := E.cut) ?_ q hq
    (E.starts_in_region _ (L.start_mem i) (hq _ q.start_mem_support))
  intro u hu w hwS huw
  by_contra hw
  exact E.no_cross u w hu hw hwS huw

theorem right_support (E : EssentialEdgeStep G A B k e)
    (R : DisjointPaths (G.deleteEdges {e}) (insert E.right E.cut) B k)
    (hR : CleanFrom R) {i : Fin k} {v : V}
    (hv : v ∈ (R.path i).support) (hvS : v ∉ E.cut) : v ∉ E.region := by
  let p := (R.path i).reverse
  have hvp : v ∈ p.support := by simpa [p] using hv
  let q := p.takeUntil v hvp
  have hq : Avoids q E.cut := by
    apply clean_prefix_avoids (R.isPath i).reverse ?_ hvp hvS
    intro w hw hwS
    exact hR i w (by simpa [p] using hw) (Finset.mem_insert_of_mem hwS)
  intro hvU
  have hqr : Avoids q.reverse E.cut := by
    intro w hw
    exact hq w (by simpa using hw)
  have hbU : R.finish i ∈ E.region := by
    apply avoiding_endpoint_in_region (S := E.cut) ?_ q.reverse hqr hvU
    intro u hu w hwS huw
    by_contra hw
    exact E.no_cross u w hu hw hwS huw
  exact E.finishes_outside _ (R.finish_mem i) (hq _ q.start_mem_support) hbU

theorem clean_families_cross (E : EssentialEdgeStep G A B k e)
    (L : DisjointPaths (G.deleteEdges {e}) A (insert E.left E.cut) k)
    (R : DisjointPaths (G.deleteEdges {e}) (insert E.right E.cut) B k)
    (hL : CleanTo L) (hR : CleanFrom R) :
    ∀ i j v, v ∈ (L.path i).support → v ∈ (R.path j).support →
      v = L.finish i ∧ v = R.start j ∧ v ∈ E.cut := by
  intro i j v hvL hvR
  have hvS : v ∈ E.cut := by
    by_contra hvS
    exact E.right_support R hR hvR hvS (E.left_support L hL hvL hvS)
  exact ⟨hL i v hvL (Finset.mem_insert_of_mem hvS),
    hR j v hvR (Finset.mem_insert_of_mem hvS), hvS⟩

end EssentialEdgeStep

end FiniteVertexMenger
end DiracBundledModule0003

/- Complete module Menger; source SHA256 7f7d2e0cd21beb75e2610f495dbaec8c8a0e990ab4de168b42b3f6faaab893c0. -/
section DiracBundledModule0004

namespace FiniteVertexMenger

variable {V : Type*} [DecidableEq V] [Fintype V]

private theorem disjointPaths_induction (m : Nat) :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.edgeFinset.card = m →
      ∀ (A B : Finset V) (k : Nat), NoSmallSeparator G A B k →
        Nonempty (DisjointPaths G A B k) := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro G _ hcount A B k hsep
    by_cases hk : k = 0
    · subst k
      exact exists_disjointPaths_zero G A B
    by_cases hbot : G = ⊥
    · subst G
      exact exists_disjointPaths_bot A B k hsep
    obtain ⟨e, he⟩ := (SimpleGraph.edgeFinset_nonempty.mpr hbot)
    let H := G.deleteEdges {e}
    have hHG : H ≤ G := G.deleteEdges_le _
    have hedges : H.edgeFinset = G.edgeFinset.erase e := by
      ext f
      simp [H, SimpleGraph.edgeSet_deleteEdges, and_comm]
    have hsmaller : H.edgeFinset.card < m := by
      rw [hedges, ← hcount]
      exact Finset.card_erase_lt_of_mem he
    by_cases hH : NoSmallSeparator H A B k
    · obtain ⟨F⟩ := ih H.edgeFinset.card hsmaller H rfl A B k hH
      exact ⟨F.mono hHG⟩
    · obtain ⟨E⟩ := essential_edge_step G A B k e (by omega) hsep he hH
      obtain ⟨L⟩ := ih H.edgeFinset.card hsmaller H rfl A
        (insert E.left E.cut) k E.left_problem
      obtain ⟨R⟩ := ih H.edgeFinset.card hsmaller H rfl
        (insert E.right E.cut) B k E.right_problem
      obtain ⟨L', hL, _, _⟩ := familyCleanTo L
      obtain ⟨R', hR, _, _⟩ := familyCleanFrom R
      exact glue_families hHG E.adjacent.ne E.left_not_mem E.right_not_mem
        E.card_cut L' R' E.adjacent (E.clean_families_cross L' R' hL hR)

theorem exists_disjointPaths_of_noSmallSeparator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (k : Nat)
    (hsep : NoSmallSeparator G A B k) :
    Nonempty (DisjointPaths G A B k) :=
  disjointPaths_induction G.edgeFinset.card G rfl A B k hsep

end FiniteVertexMenger
end DiracBundledModule0004

/- Complete module Fan; source SHA256 7ffabc24964626f4497de711a97b18bb6e2807d59110cdda9d5c2a94e052d92a. -/
section DiracBundledModule0005

namespace FiniteVertexMenger

open SimpleGraph

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
private theorem path_after_deleting_start {G : SimpleGraph V} {x t : V}
    (htx : t ≠ x) (p : G.Walk x t) (hp : p.IsPath)
    (S : Finset V) (havoid : Avoids p S) :
    ∃ u : {v : V // v ≠ x}, G.Adj x u.val ∧
      ∃ q : (G.induce {v : V | v ≠ x}).Walk u ⟨t, htx⟩,
        ∀ v ∈ q.support, v.val ∉ S := by
  cases p with
  | nil => exact (htx rfl).elim
  | @cons x u t h p =>
      have hx : x ∉ p.support := (Walk.cons_isPath_iff h p).mp hp |>.2
      have hinside : ∀ v ∈ p.support, v ∈ {v : V | v ≠ x} := by
        intro v hv h
        exact hx (h ▸ hv)
      let q := p.induce {v : V | v ≠ x} hinside
      refine ⟨⟨u, h.ne.symm⟩, h, q, ?_⟩
      intro v hv
      have hvp : v.val ∈ p.support := by
        have hmap : v.val ∈ (q.map (Embedding.induce {v : V | v ≠ x}).toHom).support := by
          rw [Walk.support_map]
          exact List.mem_map.mpr ⟨v, hv, rfl⟩
        simpa only [q, Walk.map_induce] using hmap
      exact havoid v.val (List.mem_cons_of_mem _ hvp)

theorem exists_fan_of_delete_two_connected [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : ∀ S : Finset V, S.card ≤ 2 →
      (G.induce (Set.univ \ (S : Set V))).Connected)
    (x : V) (T : Finset V) (r : Nat)
    (hx : x ∉ T) (hr : r ≤ 3) (hT : r ≤ T.card) :
    Nonempty (Fan G x T r) := by
  classical
  let W := {v : V // v ≠ x}
  let H : SimpleGraph W := G.induce {v : V | v ≠ x}
  let A : Finset W := Finset.univ.filter fun v => G.Adj x v.val
  let B : Finset W := Finset.univ.filter fun v => v.val ∈ T
  have hsep : NoSmallSeparator H A B r := by
    intro S hS
    by_contra hsmall
    have hSr : S.card < r := Nat.lt_of_not_ge hsmall
    let R : Finset V := S.image Subtype.val
    have hcard : R.card = S.card := Finset.card_image_of_injective S Subtype.val_injective
    have hRtwo : R.card ≤ 2 := by omega
    have hxR : x ∉ R := by
      intro h
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp h
      exact v.property hv
    have hRT : R.card < T.card := by omega
    obtain ⟨t, htT, htR⟩ := Finset.exists_mem_notMem_of_card_lt_card hRT
    have htx : t ≠ x := by intro h; exact hx (h ▸ htT)
    obtain ⟨p, hp⟩ := (hconn R hRtwo).exists_isPath
      ⟨x, by simp [hxR]⟩ ⟨t, by simp [htR]⟩
    let q : G.Walk x t := p.map (Embedding.induce (Set.univ \ (R : Set V))).toHom
    have hqpath : q.IsPath := hp.map Subtype.val_injective
    have hqavoid : Avoids q R := by
      intro v hv
      have hs : q.support = p.support.map
          (Embedding.induce (Set.univ \ (R : Set V))).toHom := Walk.support_map _ p
      rw [hs] at hv
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv
      exact w.property.2
    obtain ⟨u, hxu, q', hq'⟩ := path_after_deleting_start htx q hqpath R hqavoid
    have huA : u ∈ A := by simp [A, hxu]
    have htB : (⟨t, htx⟩ : W) ∈ B := by simp [B, htT]
    obtain ⟨v, hv, hvS⟩ := hS u huA ⟨t, htx⟩ htB q'
    exact hq' v hv (Finset.mem_image.mpr ⟨v, hvS, rfl⟩)
  obtain ⟨F⟩ := exists_disjointPaths_of_noSmallSeparator H A B r hsep
  obtain ⟨F, hclean, _, _⟩ := familyCleanTo F
  let inc : H →g G := (Embedding.induce {v : V | v ≠ x}).toHom
  have hsupport : ∀ i, ((F.path i).map inc).support = (F.path i).support.map Subtype.val := by
    intro i
    exact Walk.support_map inc (F.path i)
  have hstart : ∀ i, G.Adj x (F.start i).val := by
    intro i
    exact (Finset.mem_filter.mp (F.start_mem i)).2
  have hroot : ∀ i, x ∉ ((F.path i).map inc).support := by
    intro i hv
    rw [Walk.support_map] at hv
    obtain ⟨v, _, hv⟩ := List.mem_map.mp hv
    exact v.property hv
  refine ⟨{
    root_not_mem := hx
    tip := fun i => (F.finish i).val
    tip_mem := fun i => (Finset.mem_filter.mp (F.finish_mem i)).2
    tip_injective := fun i j h => F.finish_injective (Subtype.ext h)
    arm := fun i => .cons (hstart i) ((F.path i).map inc)
    isPath := fun i => ((F.isPath i).map Subtype.val_injective).cons (hroot i)
    first_contact := ?_
    disjoint_tail := ?_
  }⟩
  · intro i v hv hvT
    change v ∈ x :: ((F.path i).map inc).support at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (hx hvT).elim
    · rw [hsupport] at hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      have hwB : w ∈ B := by simp [B, hvT]
      exact congrArg Subtype.val (hclean i w hw hwB)
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    change v ∈ ((F.path i).map inc).support.toFinset at hvi
    change v ∈ ((F.path j).map inc).support.toFinset at hvj
    have hvi' := List.mem_toFinset.mp hvi
    have hvj' := List.mem_toFinset.mp hvj
    rw [hsupport] at hvi' hvj'
    obtain ⟨u, hui, hu⟩ := List.mem_map.mp hvi'
    obtain ⟨w, hwj, hw⟩ := List.mem_map.mp hvj'
    have huw : u = w := Subtype.ext (hu.trans hw.symm)
    exact Finset.disjoint_left.mp (F.disjoint hij)
      (List.mem_toFinset.mpr hui) (List.mem_toFinset.mpr (huw.symm ▸ hwj))

end FiniteVertexMenger
end DiracBundledModule0005

/- Complete module CycleSupport; source SHA256 57a9402526eb0e2df70a5db298b4df19a1146b66f09ceb00fe2ac32324559e4b. -/
section DiracBundledModule0006

namespace CorradiHajnal

open scoped SimpleGraph

def CycleOn {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) : Prop :=
  3 ≤ S.card ∧ SimpleGraph.cycleGraph S.card ⊑ G.induce (S : Set V)

theorem cycleGraph_adj_iff {n : ℕ} [NeZero n] (hn : 3 ≤ n) (i j : Fin n) :
    (SimpleGraph.cycleGraph n).Adj i j ↔ i = j + 1 ∨ j = i + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [SimpleGraph.cycleGraph_adj]
  simp only [sub_eq_iff_eq_add']

theorem CycleOn.card_ge_three {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} (h : CycleOn G S) : 3 ≤ S.card := h.1

theorem CycleOn.exists_cyclicEnumeration {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} (h : CycleOn G S) :
    ∃ f : ZMod S.card → S, Function.Bijective f ∧
      ∀ j : ZMod S.card, G.Adj (f j : V) (f (j + 1) : V) := by
  let : NeZero S.card := ⟨by have := h.1; omega⟩
  obtain ⟨c⟩ := h.2
  let e := ZMod.finEquiv S.card
  have hc : Function.Bijective c :=
    (Fintype.bijective_iff_injective_and_card c).mpr ⟨c.injective, by simp⟩
  refine ⟨fun j => c (e.symm j), hc.comp e.symm.bijective, ?_⟩
  intro j
  apply c.toHom.map_adj
  apply (cycleGraph_adj_iff h.1 _ _).mpr
  right
  simp only [map_add, map_one]

theorem cycleOn_of_cyclicEnumeration {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} (hcard : 3 ≤ S.card)
    (f : ZMod S.card → S) (hf : Function.Bijective f)
    (hadj : ∀ j : ZMod S.card, G.Adj (f j : V) (f (j + 1) : V)) :
    CycleOn G S := by
  let : NeZero S.card := ⟨by omega⟩
  let e := ZMod.finEquiv S.card
  refine ⟨hcard, ⟨{
    toHom := {
      toFun := fun i => f (e i)
      map_rel' := ?_
    }
    injective' := hf.1.comp e.injective
  }⟩⟩
  intro i j hij
  change G.Adj (f (e i) : V) (f (e j) : V)
  rcases (cycleGraph_adj_iff hcard i j).mp hij with h | h
  · subst i
    simpa only [map_add, map_one] using (hadj (e j)).symm
  · subst j
    simpa only [map_add, map_one] using hadj (e i)

theorem cycleOn_iff_cyclicEnumeration {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} :
    CycleOn G S ↔ 3 ≤ S.card ∧
      ∃ f : ZMod S.card → S, Function.Bijective f ∧
        ∀ j : ZMod S.card, G.Adj (f j : V) (f (j + 1) : V) := by
  constructor
  · intro h
    exact ⟨h.1, h.exists_cyclicEnumeration⟩
  · rintro ⟨hcard, f, hf, hadj⟩
    exact cycleOn_of_cyclicEnumeration hcard f hf hadj

theorem CycleOn.mono {V : Type*} [DecidableEq V]
    {G H : SimpleGraph V} {S : Finset V} (h : CycleOn G S) (hGH : G ≤ H) :
    CycleOn H S := by
  obtain ⟨f, hf, hadj⟩ := h.exists_cyclicEnumeration
  exact cycleOn_of_cyclicEnumeration h.1 f hf fun j => hGH (hadj j)

theorem CycleOn.map {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {S : Finset V}
    (h : CycleOn G S) (c : SimpleGraph.Copy G H) :
    CycleOn H (S.image c) := by
  have hcard : (S.image c).card = S.card :=
    Finset.card_image_of_injective S c.injective
  let d : SimpleGraph.Copy (G.induce (S : Set V))
      (H.induce ((S.image c) : Set W)) := {
    toHom := {
      toFun := fun v => ⟨c v, Finset.mem_image.mpr ⟨v, v.property, rfl⟩⟩
      map_rel' := fun hxy => c.toHom.map_adj hxy
    }
    injective' := by
      intro v w hvw
      apply Subtype.ext
      exact c.injective (congrArg Subtype.val hvw)
  }
  refine ⟨by simpa only [hcard] using h.1, ?_⟩
  rw [hcard]
  exact h.2.trans ⟨d⟩

end CorradiHajnal
end DiracBundledModule0006

/- Complete module CycleSplicing; source SHA256 0075673937a68f802c29f561a7f9d4dc86166fa74552c2f58fdcda4fd1d88c2c. -/
section DiracBundledModule0007

namespace FiniteVertexMenger

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem cycle_support_card {a : V} {p : G.Walk a a} (hp : p.IsCycle) :
    p.support.toFinset.card = p.length := by
  have hs : p.support.toFinset = p.support.tail.toFinset := by
    ext v
    simp only [List.mem_toFinset]
    constructor
    · intro hv
      rcases p.mem_support_iff.mp hv with rfl | hv
      · exact p.end_mem_tail_support hp.not_nil
      · exact hv
    · exact List.mem_of_mem_tail
  rw [hs, List.toFinset_card_of_nodup hp.support_nodup, List.length_tail,
    Walk.length_support]
  omega

theorem cycleOn_of_isCycle {a : V} {p : G.Walk a a} (hp : p.IsCycle) :
    CorradiHajnal.CycleOn G p.support.toFinset := by
  let C := p.support.toFinset
  let q := p.induce (C : Set V) (by intro v hv; exact List.mem_toFinset.mpr hv)
  have hmap : q.map (Embedding.induce (C : Set V)).toHom = p := by
    exact Walk.map_induce p _
  have hq : q.IsCycle := (Walk.map_isCycle_iff_of_injective Subtype.val_injective).mp (hmap.symm ▸ hp)
  have hlen : q.length = p.length := by
    exact (Walk.length_map _ q).symm.trans (congrArg Walk.length hmap)
  have hc : C.card = p.length := cycle_support_card hp
  refine ⟨by rw [hc]; exact hp.three_le_length, ?_⟩
  apply (cycleGraph_isContained_iff (by rw [hc]; have := hp.three_le_length; omega)).mpr
  exact ⟨_, q, hq, hlen.trans hc.symm⟩

theorem cycleOn_exists_walk {C : Finset V} (hC : CorradiHajnal.CycleOn G C)
    {a : V} (ha : a ∈ C) :
    ∃ p : G.Walk a a, p.IsCycle ∧ p.support.toFinset = C := by
  obtain ⟨v, q, hq, hlen⟩ :=
    (cycleGraph_isContained_iff (by have := hC.1; omega)).mp hC.2
  let p := q.map (Embedding.induce (C : Set V)).toHom
  have hp : p.IsCycle := hq.map Subtype.val_injective
  have hsub : p.support.toFinset ⊆ C := by
    intro w hw
    simp only [p, Walk.support_map, List.mem_toFinset, List.mem_map] at hw
    obtain ⟨z, _, rfl⟩ := hw
    exact z.property
  have heq : p.support.toFinset = C := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [cycle_support_card hp]
    exact ((Walk.length_map _ q).trans hlen).ge
  have hap : a ∈ p.support := List.mem_toFinset.mp (heq.symm ▸ ha)
  refine ⟨p.rotate hap, hp.rotate hap, ?_⟩
  ext w
  simpa only [List.mem_toFinset, Walk.mem_support_rotate_iff] using
    (Finset.ext_iff.mp heq w)

omit [DecidableEq V] in
theorem path_start_not_mem_tail {a b : V} {p : G.Walk a b} (hp : p.IsPath) :
    a ∉ p.support.tail := by
  have h := hp.support_nodup
  rw [p.support_eq_cons, List.nodup_cons] at h
  exact h.1

omit [DecidableEq V] in
theorem path_append_of_intersection {a b c : V} {p : G.Walk a b}
    {q : G.Walk b c} (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ v, v ∈ p.support → v ∈ q.support → v = b) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  intro v hvp hvq
  exact path_start_not_mem_tail hq
    (hmeet v hvp (List.mem_of_mem_tail hvq) ▸ hvq)

theorem fan_arms_meet_only_root {C : Finset V} {x : V} {r : ℕ}
    (F : Fan G x C r) {i j : Fin r} (hij : i ≠ j) {v : V}
    (hi : v ∈ (F.arm i).support) (hj : v ∈ (F.arm j).support) : v = x := by
  by_contra h
  have hit := (F.arm i).mem_support_iff.mp hi |>.resolve_left h
  have hjt := (F.arm j).mem_support_iff.mp hj |>.resolve_left h
  exact Finset.disjoint_left.mp (F.disjoint_tail hij)
    (List.mem_toFinset.mpr hit) (List.mem_toFinset.mpr hjt)

theorem fan_join {C : Finset V} {x : V} {r : ℕ}
    (F : Fan G x C r) {i j : Fin r} (hij : i ≠ j) :
    ∃ p : G.Walk (F.tip i) (F.tip j), p.IsPath ∧ 2 ≤ p.length ∧
      x ∈ p.support ∧
      (∀ v, v ∈ p.support → v ∈ C → v = F.tip i ∨ v = F.tip j) := by
  let p := (F.arm i).reverse.append (F.arm j)
  have hp : p.IsPath := by
    apply path_append_of_intersection (F.isPath i).reverse (F.isPath j)
    intro v hi hj
    exact fan_arms_meet_only_root F hij (by simpa using hi) hj
  have hxi : x ≠ F.tip i := fun h => F.root_not_mem (h.symm ▸ F.tip_mem i)
  have hxj : x ≠ F.tip j := fun h => F.root_not_mem (h.symm ▸ F.tip_mem j)
  have hli : 0 < (F.arm i).length :=
    Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hxi)
  have hlj : 0 < (F.arm j).length :=
    Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hxj)
  refine ⟨p, hp, by simp only [p, Walk.length_append, Walk.length_reverse]; omega, ?_, ?_⟩
  · apply (Walk.mem_support_append_iff _ _).mpr
    exact Or.inr (F.arm j).start_mem_support
  · intro v hv hvc
    rcases (Walk.mem_support_append_iff _ _).mp hv with hi | hj
    · exact Or.inl (F.first_contact i v (by simpa using hi) hvc)
    · exact Or.inr (F.first_contact j v hj hvc)

theorem cycle_of_fan_and_path {C : Finset V} {x : V} {r : ℕ}
    (F : Fan G x C r) {i j : Fin r} (hij : i ≠ j)
    (q : G.Walk (F.tip j) (F.tip i)) (hq : q.IsPath)
    (hsub : ∀ v, v ∈ q.support → v ∈ C) :
    ∃ D : Finset V, CorradiHajnal.CycleOn G D ∧ x ∈ D ∧
      q.support.toFinset ⊆ D ∧ 2 + q.length ≤ D.card := by
  obtain ⟨p, hp, hlen, hxp, hmeet⟩ := fan_join F hij
  have hdisj : p.support.tail.Disjoint q.support.tail := by
    intro v hvp hvq
    rcases hmeet v (List.mem_of_mem_tail hvp) (hsub v (List.mem_of_mem_tail hvq)) with h | h
    · exact path_start_not_mem_tail hp (h ▸ hvp)
    · exact path_start_not_mem_tail hq (h ▸ hvq)
  have hc := hp.isCycle_append hq hdisj (Or.inl (by omega))
  refine ⟨(p.append q).support.toFinset, cycleOn_of_isCycle hc, ?_, ?_, ?_⟩
  · exact List.mem_toFinset.mpr ((Walk.mem_support_append_iff _ _).mpr (Or.inl hxp))
  · intro v hv
    exact List.mem_toFinset.mpr
      ((Walk.mem_support_append_iff _ _).mpr (Or.inr (List.mem_toFinset.mp hv)))
  · rw [cycle_support_card hc, Walk.length_append]
    omega

omit [DecidableEq V] in
theorem cycle_support_index {a v : V} {p : G.Walk a a} (hp : p.IsCycle)
    (hv : v ∈ p.support) : ∃ n, n < p.length ∧ p.getVert n = v := by
  obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  by_cases h : n < p.length
  · exact ⟨n, h, hn⟩
  · have heq : n = p.length := by omega
    refine ⟨0, by have := hp.three_le_length; omega, ?_⟩
    simpa only [heq, Walk.getVert_length, Walk.getVert_zero] using hn

omit [DecidableEq V] in
theorem wrapped_cycle_path {a : V} {p : G.Walk a a} (hp : p.IsCycle)
    {s t : ℕ} (hst : s < t) (ht : t < p.length) :
    ((p.drop t).append (p.take s)).IsPath ∧
      (∀ v, v ∈ ((p.drop t).append (p.take s)).support → v ∈ p.support) ∧
      (∀ n, n ≤ p.length → n ≤ s ∨ t ≤ n →
        p.getVert n ∈ ((p.drop t).append (p.take s)).support) := by
  have hdrop := hp.isPath_drop (by omega : 0 < t)
  have htake := hp.isPath_take (by omega : s < p.length)
  refine ⟨path_append_of_intersection hdrop htake ?_, ?_, ?_⟩
  · intro v hvd hvt
    obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hvd
    obtain ⟨j, hj, hjl⟩ := Walk.mem_support_iff_exists_getVert.mp hvt
    simp only [Walk.drop_length] at hil
    simp only [Walk.take_length] at hjl
    have hjs : j ≤ s := le_trans hjl (Nat.min_le_left _ _)
    rw [Walk.drop_getVert] at hi
    rw [Walk.take_getVert, Nat.min_eq_right hjs] at hj
    by_cases hj0 : j = 0
    · simpa only [hj0, Walk.getVert_zero] using hj.symm
    · have heq : t + i = j := hp.getVert_injOn
        (by change 0 < _ ∧ _ ≤ _; omega)
        (by change 0 < _ ∧ _ ≤ _; omega) (hi.trans hj.symm)
      omega
  · intro v hv
    rcases (Walk.mem_support_append_iff _ _).mp hv with hv | hv
    · obtain ⟨i, hi, _⟩ := Walk.mem_support_iff_exists_getVert.mp hv
      rw [Walk.drop_getVert] at hi
      exact hi ▸ p.getVert_mem_support (t + i)
    · obtain ⟨i, hi, _⟩ := Walk.mem_support_iff_exists_getVert.mp hv
      rw [Walk.take_getVert] at hi
      exact hi ▸ p.getVert_mem_support (s ⊓ i)
  · intro n hn hside
    apply (Walk.mem_support_append_iff _ _).mpr
    rcases hside with hleft | hright
    · apply Or.inr
      apply Walk.mem_support_iff_exists_getVert.mpr
      refine ⟨n, ?_, ?_⟩
      · simp only [Walk.take_getVert, Nat.min_eq_right hleft]
      · simpa only [Walk.take_length] using le_min hleft hn
    · apply Or.inl
      apply Walk.mem_support_iff_exists_getVert.mpr
      refine ⟨n - t, ?_, ?_⟩
      · simp only [Walk.drop_getVert, Nat.add_sub_of_le hright]
      · rw [Walk.drop_length]
        omega

theorem fan_cycle_wrapped {C : Finset V} {x a : V} {r : ℕ}
    (F : Fan G x C r) {p : G.Walk a a} (hp : p.IsCycle)
    (hC : p.support.toFinset = C) {i j : Fin r} (hij : i ≠ j)
    {s t : ℕ} (hst : s < t) (ht : t < p.length)
    (hi : p.getVert s = F.tip i) (hj : p.getVert t = F.tip j) :
    ∃ D : Finset V, CorradiHajnal.CycleOn G D ∧ x ∈ D ∧
      ∀ n, n ≤ p.length → n ≤ s ∨ t ≤ n → p.getVert n ∈ D := by
  obtain ⟨hq, hsub, hkeep⟩ := wrapped_cycle_path hp hst ht
  let q := ((p.drop t).append (p.take s)).copy hj hi
  have hq' : q.IsPath := by simpa only [q, Walk.isPath_copy] using hq
  have hsub' : ∀ v, v ∈ q.support → v ∈ C := by
    intro v hv
    rw [← hC]
    exact List.mem_toFinset.mpr (hsub v (by simpa only [q, Walk.support_copy] using hv))
  obtain ⟨D, hD, hxD, hqD, _⟩ := cycle_of_fan_and_path F hij q hq' hsub'
  refine ⟨D, hD, hxD, ?_⟩
  intro n hn hside
  apply hqD
  apply List.mem_toFinset.mpr
  simpa only [q, Walk.support_copy] using hkeep n hn hside

theorem cycle_through_two_of_fan {C : Finset V} {a x : V}
    (hC : CorradiHajnal.CycleOn G C) (ha : a ∈ C) (F : Fan G x C 2) :
    ∃ D : Finset V, CorradiHajnal.CycleOn G D ∧ a ∈ D ∧ x ∈ D := by
  obtain ⟨p, hp, heq⟩ := cycleOn_exists_walk hC ha
  obtain ⟨s, hs, hsi⟩ := cycle_support_index hp
    (show F.tip 0 ∈ p.support from List.mem_toFinset.mp (by rw [heq]; exact F.tip_mem 0))
  obtain ⟨t, ht, htj⟩ := cycle_support_index hp
    (show F.tip 1 ∈ p.support from List.mem_toFinset.mp (by rw [heq]; exact F.tip_mem 1))
  have hst : s ≠ t := by
    intro h
    have htip : F.tip 0 = F.tip 1 :=
      hsi.symm.trans ((congrArg p.getVert h).trans htj)
    have := F.tip_injective htip
    omega
  rcases lt_or_gt_of_ne hst with hlt | hlt
  · obtain ⟨D, hD, hxD, hkeep⟩ :=
      fan_cycle_wrapped F hp heq (by decide : (0 : Fin 2) ≠ 1) hlt ht hsi htj
    exact ⟨D, hD, by simpa using hkeep 0 (by omega) (Or.inl (by omega)), hxD⟩
  · obtain ⟨D, hD, hxD, hkeep⟩ :=
      fan_cycle_wrapped F hp heq (by decide : (1 : Fin 2) ≠ 0) hlt hs htj hsi
    exact ⟨D, hD, by simpa using hkeep 0 (by omega) (Or.inl (by omega)), hxD⟩

theorem three_indices_same_side (f : Fin 3 → ℕ) (k : ℕ) :
    ∃ i j : Fin 3, i ≠ j ∧
      ((f i ≤ k ∧ f j ≤ k) ∨ (k ≤ f i ∧ k ≤ f j)) := by
  by_cases h0 : f 0 ≤ k
  · by_cases h1 : f 1 ≤ k
    · exact ⟨0, 1, by decide, Or.inl ⟨h0, h1⟩⟩
    · by_cases h2 : f 2 ≤ k
      · exact ⟨0, 2, by decide, Or.inl ⟨h0, h2⟩⟩
      · exact ⟨1, 2, by decide, Or.inr ⟨by omega, by omega⟩⟩
  · by_cases h1 : f 1 ≤ k
    · by_cases h2 : f 2 ≤ k
      · exact ⟨1, 2, by decide, Or.inl ⟨h1, h2⟩⟩
      · exact ⟨0, 2, by decide, Or.inr ⟨by omega, by omega⟩⟩
    · exact ⟨0, 1, by decide, Or.inr ⟨by omega, by omega⟩⟩

theorem cycle_through_three_of_fan {C : Finset V} {a b x : V}
    (hC : CorradiHajnal.CycleOn G C) (ha : a ∈ C) (hb : b ∈ C)
    (_hab : a ≠ b) (F : Fan G x C 3) :
    ∃ D : Finset V, CorradiHajnal.CycleOn G D ∧ a ∈ D ∧ b ∈ D ∧ x ∈ D := by
  classical
  obtain ⟨p, hp, heq⟩ := cycleOn_exists_walk hC ha
  have htip : ∀ i : Fin 3, ∃ n, n < p.length ∧ p.getVert n = F.tip i := by
    intro i
    exact cycle_support_index hp (List.mem_toFinset.mp (heq.symm ▸ F.tip_mem i))
  choose f hfl hf using htip
  obtain ⟨k, hk, hkb⟩ := cycle_support_index hp (List.mem_toFinset.mp (heq.symm ▸ hb))
  obtain ⟨i, j, hij, hside⟩ := three_indices_same_side f k
  have hne : f i ≠ f j := by
    intro h
    exact hij (F.tip_injective ((hf i).symm.trans ((congrArg p.getVert h).trans (hf j))))
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨D, hD, hxD, hkeep⟩ :=
      fan_cycle_wrapped F hp heq hij hlt (hfl j) (hf i) (hf j)
    refine ⟨D, hD, ?_, ?_, hxD⟩
    · simpa using hkeep 0 (by omega) (Or.inl (by omega))
    · rw [← hkb]
      apply hkeep k hk.le
      rcases hside with h | h
      · exact Or.inr h.2
      · exact Or.inl h.1
  · obtain ⟨D, hD, hxD, hkeep⟩ :=
      fan_cycle_wrapped F hp heq hij.symm hlt (hfl i) (hf j) (hf i)
    refine ⟨D, hD, ?_, ?_, hxD⟩
    · simpa using hkeep 0 (by omega) (Or.inl (by omega))
    · rw [← hkb]
      apply hkeep k hk.le
      rcases hside with h | h
      · exact Or.inr h.1
      · exact Or.inl h.2

theorem triangle_adj {C : Finset V} (hC : CorradiHajnal.CycleOn G C)
    (hthree : C.card = 3) {a b : V} (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) :
    G.Adj a b := by
  obtain ⟨c⟩ := hC.2
  have hc : Function.Bijective c :=
    (Fintype.bijective_iff_injective_and_card c).mpr ⟨c.injective, by simp⟩
  obtain ⟨i, hi⟩ := hc.2 ⟨a, ha⟩
  obtain ⟨j, hj⟩ := hc.2 ⟨b, hb⟩
  have hij : i ≠ j := by
    intro h
    apply hab
    exact (congrArg Subtype.val hi).symm.trans
      ((congrArg (fun n => (c n : V)) h).trans (congrArg Subtype.val hj))
  have htop : cycleGraph C.card = ⊤ := by
    rw [hthree]
    exact cycleGraph_three_eq_top
  have hadj : (cycleGraph C.card).Adj i j := by simpa only [htop, top_adj] using hij
  have h := c.toHom.map_adj hadj
  change G.Adj (c i : V) (c j : V) at h
  simpa only [hi, hj] using h

theorem enlarge_triangle_of_fan {C : Finset V} {x : V}
    (hC : CorradiHajnal.CycleOn G C) (hthree : C.card = 3) (F : Fan G x C 3) :
    ∃ D : Finset V, CorradiHajnal.CycleOn G D ∧ 4 ≤ D.card ∧ C ⊆ D := by
  have h20 : G.Adj (F.tip 2) (F.tip 0) :=
    triangle_adj hC hthree (F.tip_mem 2) (F.tip_mem 0)
      (fun h => (by decide : (2 : Fin 3) ≠ 0) (F.tip_injective h))
  have h01 : G.Adj (F.tip 0) (F.tip 1) :=
    triangle_adj hC hthree (F.tip_mem 0) (F.tip_mem 1)
      (fun h => (by decide : (0 : Fin 3) ≠ 1) (F.tip_injective h))
  let q : G.Walk (F.tip 2) (F.tip 1) := .cons h20 (.cons h01 .nil)
  have hq : q.IsPath := by simp [q, Walk.isPath_def, F.tip_injective.eq_iff]
  have hsub : ∀ v, v ∈ q.support → v ∈ C := by
    intro v hv
    simp only [q, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact F.tip_mem 2
    · exact F.tip_mem 0
    · exact F.tip_mem 1
  obtain ⟨D, hD, _, hqD, hcard⟩ :=
    cycle_of_fan_and_path F (by decide : (1 : Fin 3) ≠ 2) q hq hsub
  have hrange : Finset.univ.image F.tip = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact F.tip_mem i
    · rw [Finset.card_image_of_injective _ F.tip_injective]
      simp [hthree]
  refine ⟨D, hD, by simpa [q] using hcard, ?_⟩
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hrange.symm ▸ hv)
  apply hqD
  fin_cases i <;> simp [q]

end FiniteVertexMenger
end DiracBundledModule0007

/- Complete module InitialCycle; source SHA256 35a755a63552d01304fb3be017408bd309794864528ce8719250d3a43ab9a46a. -/
section DiracBundledModule0008

namespace FiniteVertexMenger

open SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}

theorem neighbor_outside_small_set
    (hn : 4 ≤ Fintype.card V)
    (hconn : ∀ S : Finset V, S.card ≤ 2 →
      (G.induce (Set.univ \ (S : Set V))).Connected)
    (a : V) (S : Finset V) (hS : S.card ≤ 2) (ha : a ∉ S) :
    ∃ b, G.Adj a b ∧ b ∉ S := by
  have hcard : (insert a S).card < (Finset.univ : Finset V).card := by
    rw [Finset.card_insert_of_notMem ha, Finset.card_univ]
    omega
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hva : v ≠ a := fun h => hv (by simp [h])
  have hvS : v ∉ S := fun h => hv (Finset.mem_insert_of_mem h)
  let a' : ↥(Set.univ \ (S : Set V)) := ⟨a, by simp [ha]⟩
  let v' : ↥(Set.univ \ (S : Set V)) := ⟨v, by simp [hvS]⟩
  have hav : a' ≠ v' := by
    intro h
    exact hva (congrArg Subtype.val h).symm
  obtain ⟨p⟩ := hconn S hS a' v'
  have hadj := p.adj_snd (Walk.not_nil_of_ne hav)
  refine ⟨(p.snd : V), hadj, ?_⟩
  exact p.snd.property.2

theorem initial_cycle
    (hn : 4 ≤ Fintype.card V)
    (hconn : ∀ S : Finset V, S.card ≤ 2 →
      (G.induce (Set.univ \ (S : Set V))).Connected)
    (a : V) :
    ∃ C : Finset V, CorradiHajnal.CycleOn G C ∧ a ∈ C := by
  obtain ⟨b, hab, _⟩ := neighbor_outside_small_set hn hconn a ∅ (by simp) (by simp)
  obtain ⟨c, hac, hcb⟩ :=
    neighbor_outside_small_set hn hconn a {b} (by simp) (by simpa using hab.ne)
  have hbc : b ≠ c := (show c ≠ b by simpa only [Finset.mem_singleton] using hcb).symm
  let b' : ↥(Set.univ \ (({a} : Finset V) : Set V)) := ⟨b, by simp [hab.ne.symm]⟩
  let c' : ↥(Set.univ \ (({a} : Finset V) : Set V)) := ⟨c, by simp [hac.ne.symm]⟩
  obtain ⟨q, hq⟩ := (hconn {a} (by simp)).exists_isPath c' b'
  let Q : G.Walk c b :=
    q.map (Embedding.induce (Set.univ \ (({a} : Finset V) : Set V))).toHom
  have hQ : Q.IsPath := hq.map Subtype.val_injective
  have hqa : a ∉ Q.support := by
    intro h
    have hs : Q.support =
        q.support.map (Embedding.induce (Set.univ \ (({a} : Finset V) : Set V))).toHom :=
      Walk.support_map _ q
    rw [hs] at h
    obtain ⟨v, _, hv⟩ := List.mem_map.mp h
    have hva : (v : V) ≠ a := by simpa using v.property.2
    exact hva hv
  let p : G.Walk b c := .cons hab.symm (.cons hac .nil)
  have hp : p.IsPath := by
    simp [p, Walk.isPath_def, hab.ne.symm, hac.ne, hbc]
  have hdisj : p.support.tail.Disjoint Q.support.tail := by
    intro v hvp hvQ
    simp only [p, Walk.support_cons, List.tail_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hvp
    rcases hvp with rfl | rfl
    · exact hqa (List.mem_of_mem_tail hvQ)
    · exact path_start_not_mem_tail hQ hvQ
  have hc := hp.isCycle_append hQ hdisj (Or.inl (by simp [p]))
  refine ⟨(p.append Q).support.toFinset, cycleOn_of_isCycle hc, ?_⟩
  apply List.mem_toFinset.mpr
  apply (Walk.mem_support_append_iff _ _).mpr
  exact Or.inl (by simp [p])

end FiniteVertexMenger
end DiracBundledModule0008

/- Complete module Main; source SHA256 a7bef53c6c083433e24e1183817fd90c29e31391e41e83065f95d70b291e29ee. -/
section DiracBundledModule0009

namespace FiniteVertexMenger

theorem cycle_through_three_vertices
    {V : Type*} [DecidableEq V] [Fintype V]
    (hn : 4 ≤ Fintype.card V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : ∀ S : Finset V, S.card ≤ 2 →
      (G.induce (Set.univ \ (S : Set V))).Connected)
    (a b c : V) (hab : a ≠ b) :
    ∃ C : Finset V, CorradiHajnal.CycleOn G C ∧ 4 ≤ C.card ∧
      a ∈ C ∧ b ∈ C ∧ c ∈ C := by
  classical
  obtain ⟨C, hC, ha⟩ := initial_cycle hn hconn a
  have htwo : ∃ D : Finset V, CorradiHajnal.CycleOn G D ∧ a ∈ D ∧ b ∈ D := by
    by_cases hb : b ∈ C
    · exact ⟨C, hC, ha, hb⟩
    · obtain ⟨F⟩ := exists_fan_of_delete_two_connected G hconn b C 2 hb
        (by decide) (by have := hC.card_ge_three; omega)
      exact cycle_through_two_of_fan hC ha F
  obtain ⟨C, hC, ha, hb⟩ := htwo
  have hthree : ∃ D : Finset V,
      CorradiHajnal.CycleOn G D ∧ a ∈ D ∧ b ∈ D ∧ c ∈ D := by
    by_cases hc : c ∈ C
    · exact ⟨C, hC, ha, hb, hc⟩
    · obtain ⟨F⟩ := exists_fan_of_delete_two_connected G hconn c C 3 hc
        (by decide) hC.card_ge_three
      exact cycle_through_three_of_fan hC ha hb hab F
  obtain ⟨C, hC, ha, hb, hc⟩ := hthree
  by_cases hfour : 4 ≤ C.card
  · exact ⟨C, hC, hfour, ha, hb, hc⟩
  have hcard : C.card = 3 := by have := hC.card_ge_three; omega
  have hlt : C.card < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨F⟩ := exists_fan_of_delete_two_connected G hconn x C 3 hx
    (by decide) hC.card_ge_three
  obtain ⟨D, hD, hDfour, hCD⟩ := enlarge_triangle_of_fan hC hcard F
  exact ⟨D, hD, hDfour, hCD ha, hCD hb, hCD hc⟩

end FiniteVertexMenger

theorem algebraDiracThreeVertices (n : ℕ) (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3conn : ∀ S : Finset (Fin n), S.card ≤ 2 →
      (G.induce (Set.univ \ (S : Set (Fin n)))).Connected)
    (v1 v2 v3 : Fin n) (h12 : v1 ≠ v2) (_h13 : v1 ≠ v3) (_h23 : v2 ≠ v3) :
    ∃ (m : ℕ) (f : ZMod m → Fin n),
      Function.Injective f ∧
      4 ≤ m ∧
      (∃ i, f i = v1) ∧ (∃ j, f j = v2) ∧ (∃ k, f k = v3) ∧
      ∀ i : ZMod m, G.Adj (f i) (f (i + 1)) := by
  obtain ⟨C, hC, hfour, h1, h2, h3⟩ :=
    FiniteVertexMenger.cycle_through_three_vertices (by simpa using hn) G h3conn
      v1 v2 v3 h12
  obtain ⟨f, hf, hadj⟩ := hC.exists_cyclicEnumeration
  refine ⟨C.card, fun i => (f i : Fin n), Subtype.val_injective.comp hf.1, hfour,
    ?_, ?_, ?_, hadj⟩
  · obtain ⟨i, hi⟩ := hf.2 ⟨v1, h1⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  · obtain ⟨i, hi⟩ := hf.2 ⟨v2, h2⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  · obtain ⟨i, hi⟩ := hf.2 ⟨v3, h3⟩
    exact ⟨i, congrArg Subtype.val hi⟩
end DiracBundledModule0009

theorem solution (n : ℕ) (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3conn : ∀ S : Finset (Fin n), S.card ≤ 2 →
      (G.induce (Set.univ \ S.toSet)).Connected)
    (v1 v2 v3 : Fin n) (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3) :
    ∃ (m : ℕ) (f : ZMod m → Fin n),
      Function.Injective f ∧
      4 ≤ m ∧
      (∃ i, f i = v1) ∧ (∃ j, f j = v2) ∧ (∃ k, f k = v3) ∧
      ∀ i : ZMod m, G.Adj (f i) (f (i + 1)) :=
  algebraDiracThreeVertices n hn G h3conn v1 v2 v3 h12 h13 h23
#print axioms solution
