-- Prove2me | solution 1 for TrailIncidence.Trail.eulerian_card_odd_degree_le_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:18:17.758329+00:00
-- url     : https://prove2.me/submissions/a01dae22-604b-4725-9620-5b5df490c81d

-- Sol generated from Bridges/TrailIncidence.lean
import Mathlib
import Definitions.Def_Bridges_TrailIncidence

/-!
# Trail incidence counting in finite undirected multigraphs

This file develops, from scratch and self-contained, a small theory of *trails* in finite
undirected multigraphs together with a complete account of **incidence counting** along a trail,
ending with the classical necessary degree condition for Eulerian trails.

## Model

A finite undirected multigraph is modelled by a vertex type `V` and an edge type `E`
(both finite with decidable equality) and an unordered endpoint map `ends : E → Sym2 V`.
Using `Sym2 V` makes the endpoints genuinely unordered and allows **parallel edges**
(distinct `e₁ e₂ : E` may have equal endpoints) and **loops** (`ends e = s(v, v)`).

A `Trail` is a walk recorded as a list of vertices `verts` and a list of edges `edges`
with `edges.length + 1 = verts.length`, a stepwise adjacency witness saying that the `i`-th
edge has endpoints `{verts[i], verts[i+1]}`, and the trail condition `edges.Nodup`
(no edge is repeated).

## Incidence count

For a vertex `v`, `incidences T v` counts, over all steps of the trail, how many of the two
endpoints of each step equal `v`.  Concretely it is the number of occurrences of `v` among the
step *tails* (`verts.dropLast`) plus the number among the step *heads* (`verts.tail`).
A loop step `v → v` therefore contributes `2` to `incidences T v`, exactly as a loop contributes
`2` to a vertex degree.

## Main results

* `Trail.sum_incidences`         : `∑ v, incidences T v = 2 * (number of trail edges)`.
* `Trail.incidences_add_endpoint`: the exact local identity
    `incidences T v + endpointContribution T v = 2 * visits T v`,
  where `visits T v` is the total number of times `v` is visited and `endpointContribution T v`
  is `1` for each of the two trail ends equal to `v` (so `2` when `v` is both start and end of a
  closed trail).
* `Trail.incidences_eq_internal` : the "twice internal pairings plus endpoint" form
    `incidences T v = 2 * internalVisits T v + endpointContribution T v`
  for a nontrivial trail (`edges ≠ []`), where `internalVisits T v` counts occurrences of `v`
  among the interior vertices.
* Parity corollaries:
  - `Trail.even_incidences_of_not_endpoint` : a non-endpoint vertex has even incidence count;
  - `Trail.odd_incidences_imp_endpoint`     : in an open trail only the two endpoints can have
    odd incidence count;
  - `Trail.even_incidences_of_closed`       : in a closed trail every vertex has even incidence
    count.
* Eulerian necessary condition:
  - `Trail.eulerian_incidences_eq_degree`            : along an Eulerian trail the incidence
    count of every vertex equals its graph degree;
  - `Trail.eulerian_card_odd_degree_le_two`          : a graph admitting an Eulerian trail has at
    most two odd-degree vertices;
  - `Trail.eulerian_closed_card_odd_degree_eq_zero`  : if the Eulerian trail is closed there are
    no odd-degree vertices.

Loops and parallel edges are fully supported by this development.
-/

open scoped BigOperators

open TrailIncidence


variable {V E : Type*}



/-! ### A list-sum lemma over a finite type -/

/-- The sum of `f` over a duplicate-free list that contains every element of a fintype equals the
sum of `f` over the whole type. -/
theorem sum_map_of_nodup_all [Fintype E] [DecidableEq E] (l : List E) (hnd : l.Nodup)
    (hall : ∀ e, e ∈ l) (f : E → ℕ) :
    (l.map f).sum = ∑ e : E, f e := by
  have hperm : List.Perm l Finset.univ.toList := by
    apply (List.perm_ext_iff_of_nodup hnd (Finset.nodup_toList _)).2
    intro e; simp [hall e]
  rw [List.Perm.sum_eq (hperm.map f), Finset.sum_map_toList]

/-! ### Edge multiplicity at a vertex -/

variable [DecidableEq V]


@[simp] theorem sym2mult_mk (a b v : V) :
    sym2mult s(a, b) v = (if a = v then 1 else 0) + (if b = v then 1 else 0) := by
  unfold sym2mult
  simp only [Sym2.toMultiset]
  by_cases h1 : a = v <;> by_cases h2 : b = v <;> simp [h1, h2, eq_comm]

/-! ### Generic list-counting lemmas -/

/-- Splitting off the head when counting in a list. -/
theorem count_eq_head_add_tail (l : List V) (v : V) :
    l.count v = (if l.head? = some v then 1 else 0) + l.tail.count v := by
  cases l with
  | nil => simp
  | cons a t =>
    simp only [List.head?_cons, List.tail_cons, List.count_cons, Option.some.injEq, beq_iff_eq]
    rw [add_comm]

/-- Splitting off the last element when counting in a list. -/
theorem count_eq_dropLast_add_getLast (l : List V) (v : V) :
    l.count v = l.dropLast.count v + (if l.getLast? = some v then 1 else 0) := by
  rcases eq_or_ne l [] with h | h
  · subst h; simp
  · conv_lhs => rw [← List.dropLast_append_getLast h]
    rw [List.count_append, List.getLast?_eq_some_getLast h]
    simp [List.count_singleton', eq_comm]



/-- The count of `v` in a list is the sum of the `{0,1}`-indicators of its entries. -/
theorem count_eq_sum_map_indicator (l : List V) (v : V) :
    l.count v = (l.map (fun x => if x = v then 1 else 0)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.count_cons, List.map_cons, List.sum_cons, ih, beq_iff_eq]
    omega

/-- Summing a pointwise sum of two equal-length `ℕ`-lists splits as the sum of the two sums. -/
theorem sum_zipWith_add (p q : List ℕ) (h : p.length = q.length) :
    (List.zipWith (· + ·) p q).sum = p.sum + q.sum := by
  induction p generalizing q with
  | nil => cases q with | nil => simp | cons b q => simp at h
  | cons a p ih =>
    cases q with
    | nil => simp at h
    | cons b q =>
      simp only [List.zipWith_cons_cons, List.sum_cons, ih q (by simpa using h)]
      omega


open Trail

variable {G : Multigraph V E} (T : Trail G)





omit [DecidableEq V] in
/-- `verts` is nonempty. -/
theorem verts_ne_nil : T.verts ≠ [] := by
  have := T.length_eq
  intro h; rw [h] at this; simp at this

/-! ### The global incidence-count theorem -/


/-! ### The local endpoint / internal-visits identity -/

/-- **Exact local identity.** The incidence count at `v` plus its endpoint contribution equals
twice the number of visits to `v`.  This is the precise statement underlying every parity
corollary below, and it holds for *all* trails (including the trivial one-vertex trail). -/
theorem incidences_add_endpoint (v : V) :
    T.incidences v + T.endpointContribution v = 2 * T.visits v := by
  have h1 := count_eq_dropLast_add_getLast T.verts v
  have h2 := count_eq_head_add_tail T.verts v
  simp only [incidences, endpointContribution, visits] at *
  omega


/-! ### Parity corollaries -/

/-- A vertex that is neither the start nor the end of the trail has even incidence count. -/
theorem even_incidences_of_not_endpoint {v : V}
    (h1 : T.verts.head? ≠ some v) (h2 : T.verts.getLast? ≠ some v) :
    Even (T.incidences v) := by
  have h := incidences_add_endpoint T v
  simp only [endpointContribution, if_neg h1, if_neg h2, add_zero] at h
  exact ⟨T.visits v, by omega⟩



/-! ### Bridge to graph degree and the Eulerian condition -/

/-- The list of per-edge multiplicities of `v` along the trail equals the pointwise sum of the
two endpoint indicators along the consecutive-vertex pairs. -/
theorem map_sym2mult_eq_zipWith (v : V) :
    T.edges.map (fun e => sym2mult (G.ends e) v)
      = List.zipWith (fun a b => (if a = v then 1 else 0) + (if b = v then 1 else 0))
          T.verts.dropLast T.verts.tail := by
  have hlen := T.length_eq
  apply List.ext_getElem
  · simp [List.length_zipWith, List.length_dropLast, List.length_tail]; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_zipWith]
    have hi : i < T.edges.length := by simpa using h1
    have hadj := T.adj ⟨i, hi⟩
    rw [List.get_eq_getElem] at hadj
    simp only [hadj, sym2mult_mk, List.getElem_dropLast, List.getElem_tail, List.get_eq_getElem]

/-- **Bridge lemma.** The trail-incidence count of `v` equals the sum over the trail edges of the
edge multiplicity of `v`.  This connects the positional incidence count to the graph structure. -/
theorem incidences_eq_sum_edges (v : V) :
    T.incidences v = (T.edges.map (fun e => sym2mult (G.ends e) v)).sum := by
  rw [incidences, map_sym2mult_eq_zipWith]
  rw [show (List.zipWith (fun a b => (if a = v then 1 else 0) + (if b = v then 1 else 0))
            T.verts.dropLast T.verts.tail)
        = List.zipWith (· + ·) (T.verts.dropLast.map (fun x => if x = v then 1 else 0))
            (T.verts.tail.map (fun x => if x = v then 1 else 0)) from List.zipWith_map.symm]
  rw [sum_zipWith_add _ _ (by simp [List.length_dropLast, List.length_tail]),
      ← count_eq_sum_map_indicator, ← count_eq_sum_map_indicator]


/-- Along an Eulerian trail the incidence count of each vertex equals its graph degree. -/
theorem eulerian_incidences_eq_degree [Fintype E] [DecidableEq E]
    (hEul : T.IsEulerian) (v : V) : T.incidences v = G.degree v := by
  rw [incidences_eq_sum_edges, Multigraph.degree]
  exact sum_map_of_nodup_all T.edges T.nodup hEul _





open TrailIncidence.Trail
open TrailIncidence.Trail
namespace TrailIncidence.Trail
/-- `verts` is nonempty. -/
theorem verts_ne_nil : T.verts ≠ [] := by
  have := T.length_eq
  intro h; rw [h] at this; simp at this

end TrailIncidence.Trail

namespace TrailIncidence.Trail
/-- A vertex that is neither the start nor the end of the trail has even incidence count. -/
theorem even_incidences_of_not_endpoint {v : V}
    (h1 : T.verts.head? ≠ some v) (h2 : T.verts.getLast? ≠ some v) :
    Even (T.incidences v) := by
  have h := incidences_add_endpoint T v
  simp only [endpointContribution, if_neg h1, if_neg h2, add_zero] at h
  exact ⟨T.visits v, by omega⟩

end TrailIncidence.Trail

open Trail in
theorem solution[Fintype V] [Fintype E] [DecidableEq E]
    (hEul : T.IsEulerian) :
    (Finset.univ.filter (fun v => Odd (G.degree v))).card ≤ 2 := by
  have hne := T.verts_ne_nil
  have hsub : (Finset.univ.filter (fun v => Odd (G.degree v)))
      ⊆ {T.verts.head hne, T.verts.getLast hne} := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rw [← eulerian_incidences_eq_degree T hEul v] at hv
    by_contra hcon
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcon
    push_neg at hcon
    have h1 : T.verts.head? ≠ some v := by
      rw [List.head?_eq_some_head hne]; simp; exact fun h => hcon.1 h.symm
    have h2 : T.verts.getLast? ≠ some v := by
      rw [List.getLast?_eq_some_getLast hne]; simp; exact fun h => hcon.2 h.symm
    exact (Nat.not_odd_iff_even.mpr (T.even_incidences_of_not_endpoint h1 h2)) hv
  refine (Finset.card_le_card hsub).trans ?_
  exact (Finset.card_insert_le _ _).trans (by simp)
