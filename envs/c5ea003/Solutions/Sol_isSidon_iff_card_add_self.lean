-- Prove2me | solution 1 for isSidon_iff_card_add_self
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T21:19:13.821416+00:00
-- url     : https://prove2.me/submissions/652aa717-d714-4426-a567-25b867503447

-- Sol generated from Shared/SidonSetsRigidity.lean
import Mathlib
import Definitions.Def_Shared_SidonSetsErdosTuran
import Definitions.Def_Shared_SidonSetsRigidity
import Theorems.Thm_addSelf_eq_image_sym2

/-!
# Sidon sets II: counting characterisations, extremal rigidity, and Reiman double counting

This file is the second cycle of the Sidon-set research thread begun in
`Shared/SidonSetsErdosTuran.lean`.  There we established the Erdős–Turán sandwich
`√(N/8) < maxSidonCard N ≤ √(2N) + 1` and the dictionary
"Sidon set ⟺ `C₄`-free bipartite incidence graph".  Here we push on three
consequences of that dictionary.

## Main results

Counting characterisation (`Sym2`-valued):

* `addSelf_eq_image_sym2` — the sumset `A + A` is the image of the unordered-pair
  finset `A.sym2` under addition.
* `card_add_self_le` — hence `|A + A| ≤ C(|A| + 1, 2)` for *every* finite set.
* `isSidon_iff_card_add_self` — **`A` is a Sidon set precisely when its sumset is
  as large as it can possibly be**, `|A + A| = C(|A| + 1, 2)`.  This converts the
  Sidon property from a `∀`-statement about quadruples into a single cardinality
  equation.

Extremal rigidity (perfect difference sets):

* `IsSidon.card_diffSet` — a Sidon set realises exactly `|A|² - |A|` nonzero
  differences.
* `IsSidon.perfect_iff` — **the Sidon bound `|A|(|A| - 1) ≤ |G| - 1` is attained iff
  the difference set is all of `G ∖ {0}`**, i.e. iff `A` is a perfect difference set.
* `IsSidon.exists_unique_diff` — at the extremum every nonzero group element has a
  *unique* ordered representation `g = a - b` with `a, b ∈ A`.

Reiman / Kővári–Sós–Turán double counting:

* `sum_offDiag_card_le_of_unique_common_neighbour` — a general extremal-graph-theory
  lemma, absent from Mathlib: in any bipartite incidence system where two distinct
  left vertices share at most one common neighbour, `∑_y (d(y)² - d(y)) ≤ |X|² - |X|`.
* `IsSidon.card_bound_via_reiman` — feeding the Sidon incidence graph into that lemma
  gives a **second, purely graph-theoretic proof** of `|A|(|A| - 1) ≤ |G| - 1`,
  logically independent of the difference-injection proof of cycle 1.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): Cycle 1 revealed that the Sidon condition is a *rigidity*
  phenomenon (unique representation).  Three refinements were conjectured.
  (R1) Rigidity is equivalent to an extremal *count*: `A` is Sidon iff `|A+A|` hits
       the trivial upper bound `C(|A|+1,2)`.
  (R2) The inequality `|A|(|A|-1) ≤ |G|-1` is *self-improving*: equality forces the
       difference set to be all of `G ∖ {0}` (a perfect difference set), so the
       extremal configurations are completely rigid, not merely maximal.
  (R3) The `C₄`-free dictionary is strong enough to reprove the counting bound from
       pure graph theory, via a Reiman-type cherry count, with no additive input
       beyond the degree computation `d(y) = |A|`.
Experiment (Experimenter): (R1) was proved by exhibiting `A + A` as the image of
  `Finset.sym2 A` under `Sym2.lift (+)`; the Sidon property is *exactly* injectivity
  of that map, so `Finset.card_image_of_injOn` and `Finset.injOn_of_card_image_eq`
  give the two directions.  (R2) was proved with
  `Finset.eq_of_subset_of_card_le`: the difference set is contained in `G ∖ {0}` and
  has the same cardinality at the extremum.  (R3) required a new general lemma; the
  cherry sets `(N y).offDiag` are pairwise disjoint exactly because two left vertices
  have at most one common neighbour, so `Finset.card_biUnion` turns the double count
  into a single cardinality comparison.
Analysis (Analyst): The three results are three faces of one fact — the Sidon
  property is injectivity of a *single* explicitly constructed map.  Choosing the map
  to be `Sym2 A → A + A` gives the counting characterisation; choosing it to be
  `A.offDiag → G ∖ {0}` gives the difference bound and its rigidity; choosing it to be
  the disjointness of cherry sets gives the Reiman bound.  Nothing here needs the
  ambient set to be an interval or a group of any particular shape, so all three
  survive verbatim in `ZMod N`.
Critique (Critic): `sum_offDiag_card_le_of_unique_common_neighbour` is stated for an
  arbitrary neighbourhood family `N : Y → Finset X`, so it is not tailored to make the
  Sidon application easy — the application must supply the degree computation itself.
  `IsSidon.card_bound_via_reiman` genuinely avoids `IsSidon.sub_injOn`: it invokes the
  Sidon hypothesis only through the four-element identity
  `(y - x) + (y' - x') = (y - x') + (y' - x)`.  `IsSidon.exists_unique_diff` is
  conditional on attaining the extremum, which is exactly the guarded boundary: for a
  generic group order no perfect difference set exists, and the theorem says nothing
  in that case.
Synthesis (PI): one injectivity, three cardinality consequences; rigidity at the
  extremum; and an independent graph-theoretic route to the same bound.
-/

open Finset Pointwise

variable {M : Type*} [AddCancelCommMonoid M] [DecidableEq M] {A : Finset M}








variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {A : Finset G}







/-! ## Reiman-type double counting for `K_{2,2}`-free incidence systems -/


variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {A : Finset G}




open Sym2 in
theorem solution {M : Type*} [AddCancelCommMonoid M] [DecidableEq M] {A : Finset M} :
    IsSidon A ↔ #(A + A) = (#A + 1).choose 2 := by
  rw [addSelf_eq_image_sym2, ← Finset.card_sym2 A]
  constructor
  · intro hA
    refine Finset.card_image_of_injOn ?_
    intro m hm m' hm' h
    induction m with
    | _ a b =>
      induction m' with
      | _ c d =>
        simp only [Finset.mem_coe, Finset.mem_sym2_iff] at hm hm'
        have ha : a ∈ A := hm a (Sym2.mem_mk_left a b)
        have hb : b ∈ A := hm b (Sym2.mem_mk_right a b)
        have hc : c ∈ A := hm' c (Sym2.mem_mk_left c d)
        have hd : d ∈ A := hm' d (Sym2.mem_mk_right c d)
        have hsum : a + b = c + d := h
        rcases hA a ha b hb c hc d hd hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [Sym2.eq_iff]; exact Or.inr ⟨h1, h2⟩
  · intro hcard
    have hinj := Finset.injOn_of_card_image_eq hcard
    intro a ha b hb c hc d hd hsum
    have hma : s(a, b) ∈ (A.sym2 : Set (Sym2 M)) := by
      simp only [Finset.mem_coe, Finset.mem_sym2_iff]
      intro z hz; rcases Sym2.mem_iff.mp hz with rfl | rfl <;> assumption
    have hmc : s(c, d) ∈ (A.sym2 : Set (Sym2 M)) := by
      simp only [Finset.mem_coe, Finset.mem_sym2_iff]
      intro z hz; rcases Sym2.mem_iff.mp hz with rfl | rfl <;> assumption
    have := hinj hma hmc (by simpa using hsum)
    exact Sym2.eq_iff.mp this
