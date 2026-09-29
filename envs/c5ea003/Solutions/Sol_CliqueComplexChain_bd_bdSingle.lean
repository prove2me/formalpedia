-- Prove2me | solution 1 for CliqueComplexChain.bd_bdSingle
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:17:08.849168+00:00
-- url     : https://prove2.me/submissions/4318db7c-1675-4b9b-815c-2c0fa98ab520

-- Sol generated from Shared/RamseyTheory/CliqueComplexChain.lean
import Mathlib
import Definitions.Def_Shared_RamseyTheory_CliqueComplexChain
/-
# The Simplicial Chain Complex of a Clique Complex over ℤ

The clique complex `Δ(G)` of a simple graph `G` is the abstract simplicial complex
whose `k`-faces are the `(k+1)`-cliques of `G`.  Choosing a linear order on the
vertex set turns the set of finite cliques into an *ordered* simplicial complex,
and the standard alternating-sum boundary operator

  ∂(s) = Σ_{x ∈ s} (-1)^{rank of x in s} · (s \ {x})

makes the free ℤ-modules on faces into a chain complex.

This file develops that chain complex purely combinatorially on `Finset V →₀ ℤ`
(the free ℤ-module on all finite subsets, of which the clique complex is a
downward-closed sub-object) and proves the defining identity `∂ ∘ ∂ = 0`.
We then connect it back to graphs: cliques are downward closed, and the boundary
of a clique-face is supported on clique-faces, so the construction restricts to a
genuine chain complex of `Δ(G)`.

The novelty here is a fully self-contained, order-theoretic proof of `∂² = 0`
via a sign-reversing involution on ordered pairs of vertices, packaged so that it
applies verbatim to the clique complex of an arbitrary simple graph.
-/

open Finset SimpleGraph

open CliqueComplexChain

variable {V : Type*} [LinearOrder V]




-- !-- Evaluating the linear boundary on a basis chain just scales `bdSingle`. -- !--

/-
!-- If `x ∉ s` is not below `y`, erasing `x` does not change the rank of `y`,
so the sign is unchanged.  Uses `Finset.filter_erase`. -- !--
-/
lemma sgn_erase_not_lt {s : Finset V} {x y : V} (h : ¬ x < y) :
    sgn y (s.erase x) = sgn y s := by
  unfold sgn;
  rw [ Finset.filter_erase ] ; aesop

/-
!-- If `x ∈ s` lies below `y`, erasing `x` drops the rank of `y` by one, so the
sign flips.  Uses `Finset.filter_erase` and `(-1)^(n+1) = -(-1)^n`. -- !--
-/
lemma sgn_erase_lt {s : Finset V} {x y : V} (hx : x ∈ s) (h : x < y) :
    sgn y (s.erase x) = - sgn y s := by
  unfold sgn; simp +decide [ *, Finset.filter_erase ] ;
  rw [ ← Nat.sub_add_cancel ( show 1 ≤ # ( { x ∈ s | x < y } ) from Finset.card_pos.mpr ⟨ x, by aesop ⟩ ), pow_succ' ] ; ring!;

/-
!-- Core sign-cancellation: the two ways of removing an unordered pair `{x,y}`
from `s` carry opposite signs.  Case split on the trichotomy of `x` and `y`,
using `sgn_erase_lt` / `sgn_erase_not_lt`. -- !--
-/
lemma sgn_swap {s : Finset V} {x y : V} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    sgn x s * sgn y (s.erase x) = - (sgn y s * sgn x (s.erase y)) := by
  cases lt_or_gt_of_ne hxy <;> simp_all +decide [ sgn_erase_lt ];
  · grind +suggestions;
  · rw [ sgn_erase_not_lt ];
    · ring;
    · exact not_lt_of_gt ‹_›

/-
!-- The boundary of a boundary of one simplex vanishes.  Expand into a double
sum over ordered pairs `(x,y)`, reindex over `s.sigma (fun x => s.erase x)`,
and kill it with `Finset.sum_involution` using the swap `(x,y) ↦ (y,x)`:
paired terms hit the same face `(s.erase x).erase y = (s.erase y).erase x`
(`Finset.erase_right_comm`) with opposite signs by `sgn_swap`. -- !--
-/

/-
!-- `∂² = 0` on every chain, by `Finsupp.induction` reducing to `bd_bdSingle`. -- !--
-/

-- !-- The chain-complex identity `∂ ∘ ∂ = 0` as linear maps. -- !--

/-! ## Connection to the clique complex of a graph -/


-- !-- Faces are downward closed: a subset of a clique is a clique
-- (`SimpleGraph.IsClique.subset`). -- !--

-- !-- The empty face is always present. -- !--

-- !-- Every vertex is a `0`-face. -- !--

/-
!-- The boundary of a clique-face is supported on clique-faces, so `∂` really
maps clique-chains to clique-chains.  Each support element is some `s.erase x`,
a subset of `s`, hence a face by `isFace_downward_closed`. -- !--
-/


open CliqueComplexChain in
lemma solution(s : Finset V) : bd (bdSingle s) = 0 := by
  unfold bd bdSingle;
  simp +decide [ Finset.smul_sum ];
  -- By pairing each term with its negative counterpart, we can show that the sum is zero.
  have h_pair : ∀ x ∈ s, ∀ y ∈ s.erase x, (Finsupp.single ((s.erase x).erase y) (sgn x s)) * (Finsupp.single ((s.erase x).erase y) (sgn y (s.erase x))) + (Finsupp.single ((s.erase y).erase x) (sgn y s)) * (Finsupp.single ((s.erase y).erase x) (sgn x (s.erase y))) = 0 := by
    intro x hx y hy; ext z; simp +decide [ Finsupp.single_apply, Finset.erase_right_comm ] ;
    split_ifs <;> simp_all +decide [ sgn_swap ];
  have h_sum_zero : ∑ x ∈ s, ∑ y ∈ s.erase x, (Finsupp.single ((s.erase x).erase y) (sgn x s)) * (Finsupp.single ((s.erase x).erase y) (sgn y (s.erase x))) = ∑ x ∈ s, ∑ y ∈ s.erase x, (Finsupp.single ((s.erase y).erase x) (sgn y s)) * (Finsupp.single ((s.erase y).erase x) (sgn x (s.erase y))) := by
    rw [ Finset.sum_sigma', Finset.sum_sigma' ];
    apply Finset.sum_bij (fun x _ => ⟨x.snd, x.fst⟩);
    · aesop;
    · aesop;
    · aesop;
    · grind;
  have h_sum_zero : ∑ x ∈ s, ∑ y ∈ s.erase x, (Finsupp.single ((s.erase x).erase y) (sgn x s)) * (Finsupp.single ((s.erase x).erase y) (sgn y (s.erase x))) + ∑ x ∈ s, ∑ y ∈ s.erase x, (Finsupp.single ((s.erase y).erase x) (sgn y s)) * (Finsupp.single ((s.erase y).erase x) (sgn x (s.erase y))) = 0 := by
    simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => h_pair x hx y hy;
  simp_all +decide [ ← two_smul ℤ ]
