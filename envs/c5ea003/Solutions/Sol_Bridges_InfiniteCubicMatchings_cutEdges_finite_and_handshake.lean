-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.cutEdges_finite_and_handshake
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T13:45:32.964259+00:00
-- url     : https://prove2.me/submissions/d9777a70-8019-499d-bad0-ffb430e9cb42

-- Sol generated from Bridges/InfiniteCubicMatchingsBridgeParity.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridgeParity
import Theorems.Thm_Bridges_InfiniteCubicMatchings_even_card_of_involutive
/-
# Cut parity in cubic graphs, and bridges versus finite sides

`InfiniteCubicMatchings.lean` proves that a graph possessing a **one-edge odd cut** satisfies
none of the three properties (`not_bergeFulkerson_of_oddCut_singleton` and friends), where
`IsOddCut G {e}` asks for a finite vertex set `S` of *odd* cardinality with
`cutEdges G S = {e}`.  In the finite world one never checks that parity by hand: a cubic graph
with a bridge automatically has an odd side, by the handshake lemma.  In the infinite world the
argument has to be redone for a *finite side of a possibly infinite graph*, and doing so was
next-cycle sub-conjecture 3 of `FUTURE_DIRECTIONS.md`.

This file proves it, in the sharpest form available.  The engine is
`cutEdges_finite_and_handshake`: for a cubic graph and **any** finite vertex set `S`, the cut
`cutEdges G S` is finite and

  `3 * S.card = 2 * m + (cutEdges G S).ncard`   for some `m`,

by a half-edge count — the set of pairs `(v, w)` with `v ∈ S` and `v` adjacent to `w` has
exactly `3 * S.card` elements; the pairs with `w ∈ S` form a set stable under a fixed-point-free
involution (swap), hence of even size; and the pairs with `w ∉ S` are in bijection with the cut.
Consequently `S.card` and `(cutEdges G S).ncard` always have the *same parity*
(`odd_card_iff_odd_ncard_cutEdges`), which is the infinite-graph form of the classical
"odd side ⟺ odd cut" for cubic graphs.

Consequences:

* `isOddCut_iff_odd_ncard` : for a cubic graph, `C` is an odd cut in the sense of `IsOddCut`
  iff it is the cut of some finite vertex set and has an odd number of edges;
* `isOddCut_singleton_iff` : in particular the parity hypothesis is automatic for one-edge
  cuts, so the obstruction in `not_bergeFulkerson_of_oddCut_singleton` is exactly
  "a one-edge cut with a finite side";
* `cutEdgesSet_bridgeSide` : the vertex set reachable from `u` after deleting a bridge
  `s(u, w)` has exactly `{s(u, w)}` as its cut;
* `not_bergeFulkerson_of_bridge_with_finite_side` (and the `FanRaspaud` / `MacajovaSkoviera`
  versions) : a cubic graph with a bridge one of whose sides is finite satisfies none of the
  three properties;
* `bridge_sides_infinite_of_bergeFulkerson` : hence, in a cubic graph satisfying
  Berge–Fulkerson, **every bridge separates two infinite sides**.  Together with
  `exists_bridged_cubic_bergeFulkerson` of `…Bridged.lean` this is sharp; the two halves are
  combined in `…BridgeSharp.lean`.
-/

open Bridges.InfiniteCubicMatchings

universe u

variable {V : Type u} {G : SimpleGraph V}

/-! ## The half-edge count -/

/-- In a cubic graph every neighbour set is finite (an infinite set has `ncard = 0`). -/
lemma IsCubic.neighborSet_finite (hG : IsCubic G) (v : V) : (G.neighborSet v).Finite :=
  Set.finite_of_ncard_ne_zero (by rw [hG v]; omega)








/-! ## Bridges -/













open Bridges.InfiniteCubicMatchings in
theorem solution(hG : IsCubic G) (S : Finset V) :
    (cutEdges G S).Finite ∧ ∃ m : ℕ, 3 * S.card = 2 * m + (cutEdges G S).ncard := by
  classical
  have hfin : ∀ v : V, (G.neighborSet v).Finite := IsCubic.neighborSet_finite hG
  -- the neighbours of `v`, as a `Finset`
  set N : V → Finset V := fun v => (hfin v).toFinset with hNdef
  have hNmem : ∀ v w : V, w ∈ N v ↔ G.Adj v w := by
    intro v w
    simp [hNdef]
  have hNcard : ∀ v, (N v).card = 3 := by
    intro v
    have h3 := hG v
    rwa [Set.ncard_eq_toFinset_card _ (hfin v)] at h3
  -- the half-edges based in `S`
  set D : Finset (V × V) := S.biUnion (fun v => (N v).image (fun w => (v, w))) with hDdef
  have hDmem : ∀ p : V × V, p ∈ D ↔ p.1 ∈ S ∧ G.Adj p.1 p.2 := by
    rintro ⟨a, b⟩
    constructor
    · intro hp
      rw [hDdef, Finset.mem_biUnion] at hp
      obtain ⟨v, hvS, hv⟩ := hp
      rw [Finset.mem_image] at hv
      obtain ⟨w, hw, hvw⟩ := hv
      cases hvw
      exact ⟨hvS, (hNmem _ _).mp hw⟩
    · rintro ⟨haS, hab⟩
      rw [hDdef, Finset.mem_biUnion]
      exact ⟨a, haS, Finset.mem_image.mpr ⟨b, (hNmem _ _).mpr hab, rfl⟩⟩
  have hDcard : D.card = 3 * S.card := by
    rw [hDdef, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun v _ => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
      rw [Finset.card_image_of_injective _ (fun x y hxy => (Prod.mk.injEq _ _ _ _ ▸ hxy).2),
        hNcard v]
    · intro x _ y _ hxy
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      rintro ⟨a, b⟩ hx hy
      rw [Finset.mem_image] at hx hy
      obtain ⟨wx, -, hax⟩ := hx
      obtain ⟨wy, -, hay⟩ := hy
      rw [Prod.mk.injEq] at hax hay
      exact hxy (hax.1.trans hay.1.symm)
  -- split into inner and outgoing half-edges
  have hsplit : (D.filter fun p => p.2 ∈ S).card + (D.filter fun p => p.2 ∉ S).card = D.card :=
    Finset.card_filter_add_card_filter_not _
  -- the inner half-edges are permuted by `swap`, a fixed-point-free involution, so there is an
  -- even number of them
  have hinner : Even (D.filter fun p => p.2 ∈ S).card := by
    refine even_card_of_involutive _ Prod.swap ?_ (fun a _ => Prod.swap_swap a) ?_
    · rintro ⟨a, b⟩ hp
      rw [Finset.mem_filter, hDmem] at hp
      obtain ⟨⟨haS, hab⟩, hbS⟩ := hp
      rw [Finset.mem_filter, hDmem]
      exact ⟨⟨hbS, hab.symm⟩, haS⟩
    · rintro ⟨a, b⟩ hp
      rw [Finset.mem_filter, hDmem] at hp
      intro hcon
      exact hp.1.2.ne (congrArg Prod.fst hcon).symm
  -- the outgoing half-edges are in bijection with the cut
  set E : Finset (Sym2 V) := (D.filter fun p => p.2 ∉ S).image (fun p => s(p.1, p.2)) with hEdef
  have hEcoe : (↑E : Set (Sym2 V)) = cutEdges G S := by
    ext f
    constructor
    · intro hf
      rw [Finset.mem_coe, hEdef, Finset.mem_image] at hf
      obtain ⟨p, hp, rfl⟩ := hf
      rw [Finset.mem_filter, hDmem] at hp
      exact ⟨hp.1.2, p.1, p.2, rfl, hp.1.1, hp.2⟩
    · rintro ⟨hfE, a, b, rfl, haS, hbS⟩
      rw [Finset.mem_coe, hEdef, Finset.mem_image]
      exact ⟨(a, b), by rw [Finset.mem_filter, hDmem]; exact ⟨⟨haS, hfE⟩, hbS⟩, rfl⟩
  have hEcard : E.card = (D.filter fun p => p.2 ∉ S).card := by
    rw [hEdef]
    refine Finset.card_image_of_injOn ?_
    rintro ⟨a, b⟩ hp ⟨c, d⟩ hq hpq
    rw [Finset.mem_coe, Finset.mem_filter, hDmem] at hp hq
    rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Prod.mk.injEq]
      exact ⟨h1, h2⟩
    · exact absurd (h1 ▸ hp.1.1) hq.2
  have hncard : (cutEdges G S).ncard = (D.filter fun p => p.2 ∉ S).card := by
    rw [← hEcoe, Set.ncard_coe_finset, hEcard]
  refine ⟨hEcoe ▸ E.finite_toSet, ?_⟩
  obtain ⟨m, hm⟩ := hinner
  refine ⟨m, ?_⟩
  rw [hncard]
  omega
