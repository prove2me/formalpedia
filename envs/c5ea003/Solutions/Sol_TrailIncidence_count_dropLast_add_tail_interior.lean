-- Prove2me | solution 1 for TrailIncidence.count_dropLast_add_tail_interior
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:01:08.654259+00:00
-- url     : https://prove2.me/submissions/b63efae1-2c1b-42c5-91c6-8ab2b04fd648

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


/-! ### Edge multiplicity at a vertex -/

variable [DecidableEq V]



/-! ### Generic list-counting lemmas -/


/-- Splitting off the last element when counting in a list. -/
theorem count_eq_dropLast_add_getLast (l : List V) (v : V) :
    l.count v = l.dropLast.count v + (if l.getLast? = some v then 1 else 0) := by
  rcases eq_or_ne l [] with h | h
  · subst h; simp
  · conv_lhs => rw [← List.dropLast_append_getLast h]
    rw [List.count_append, List.getLast?_eq_some_getLast h]
    simp [List.count_singleton', eq_comm]






open Trail

variable {G : Multigraph V E} (T : Trail G)






/-! ### The global incidence-count theorem -/


/-! ### The local endpoint / internal-visits identity -/



/-! ### Parity corollaries -/




/-! ### Bridge to graph degree and the Eulerian condition -/









theorem solution(l : List V) (v : V) (hl : 2 ≤ l.length) :
    l.dropLast.count v + l.tail.count v
      = 2 * l.tail.dropLast.count v
        + (if l.head? = some v then 1 else 0) + (if l.getLast? = some v then 1 else 0) := by
  match l, hl with
  | a :: t, hl =>
    have ht : t ≠ [] := by intro h; subst h; simp at hl
    have hdl : (a :: t).dropLast = a :: t.dropLast := List.dropLast_cons_of_ne_nil ht
    have hgl : (a :: t).getLast? = t.getLast? := by
      cases t with
      | nil => simp at ht
      | cons b s => rw [List.getLast?_cons_cons]
    have hcount_t := count_eq_dropLast_add_getLast t v
    simp only [hdl, List.tail_cons, List.head?_cons, hgl, List.count_cons, Option.some.injEq,
      beq_iff_eq]
    rw [hcount_t]
    by_cases hav : a = v <;> simp [hav] <;> omega
