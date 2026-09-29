-- Prove2me | solution 1 for DreamLogic.Topo.closed_not_iUnion_closed
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:41:51.876265+00:00
-- url     : https://prove2.me/submissions/27e42869-5457-4a46-a87c-56c1b150b5a9

-- Sol generated from Logic/DreamLogic/ClosedSetTopology.lean
import Mathlib
import Definitions.Def_Logic_DreamLogic_ClosedSetTopology

/-!
# Dream Logic II — Closed-Set Semantics and the Failure of Arbitrary Union

This file gives the *topological* face of dream logic. In the standard intuitionistic
topological semantics, propositions are **open** sets and negation is the interior of the
complement; the law of non-contradiction holds and excluded middle fails. Dream logic is the
exact dual: propositions are **closed** sets and negation is the *closure of the complement*,

  `pneg A = closure Aᶜ`.

In this closed-set semantics contradictions genuinely coexist — a set and its negation can
overlap on their shared boundary — and the structural obstruction that makes the logic
paraconsistent is precisely that **closed sets are not closed under arbitrary union**.

## Main results

* `isClosed_pneg` — the paraconsistent negation of any set is a legitimate (closed) proposition.
* `lem_closed_holds` — the law of excluded middle *survives* for closed propositions:
  `A ∪ pneg A = univ`.
* `contradiction_coexists` — the law of non-contradiction *fails*: there is a closed set
  meeting its own negation, an "impossible object" living on the boundary.
* `closed_not_iUnion_closed` — the structural root of paraconsistency: a countable family of
  closed sets whose union fails to be closed.
* `frontier_is_glut` — boundary points are exactly the gluts: they lie in a closed set and in
  its paraconsistent negation simultaneously.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): Dream logic should be modelled by *closed* subsets of a
topological space with `pneg A = closure Aᶜ`. If so, the impossible objects of the algebraic
model must appear as concrete geometric objects, and the paraconsistency must be traceable to
a specific topological failure — the non-closure of arbitrary unions of closed sets.

Experiment (Experimenter): Work over `ℝ` with its order topology. Take the model proposition
`A = [0,1]`. Compute `pneg A`, its overlap with `A`, and test excluded middle and
non-contradiction. Separately, build the family `[1/(n+1), 1]` and evaluate its union.

Analysis (Analyst): `A ∩ pneg A` is exactly the topological frontier `{0,1}` — the boundary
points are the gluts. Excluded middle holds trivially because `Aᶜ ⊆ pneg A`. The union
`⋃ₙ [1/(n+1),1] = (0,1]` is *not* closed: the infimum `0` is a limit point outside it. This
missing closure is the same phenomenon that, read logically, blocks the inference "if a
contradiction holds then everything holds" — infinite disjunction does not preserve truth.

Critique (Critic): The coexistence witness is a nonempty overlap given by an explicit point,
so the theorem is not vacuous. The union counterexample uses a genuine limit argument
(`closure (0,1] = [0,1]`), not a definitional trick. All statements quantify over honest
objects of `ℝ` and are proved with real topological lemmas (`closure_Ioc`, `closure_Iio`,
`isClosed_Icc`).

Synthesis (PI): The closed-set model realizes the algebraic dream logic geometrically:
gluts are boundary points, and the paraconsistency is the shadow of arbitrary unions of
closed sets escaping closedness. The bridge to the four-valued algebra is made explicit in
`Correspondence.lean`.
-/

open DreamLogic.Topo

open Set







open DreamLogic.Topo in
theorem solution:
    ∃ F : ℕ → Set ℝ, (∀ n, IsClosed (F n)) ∧ ¬ IsClosed (⋃ n, F n) := by
  refine ⟨fun n => Icc (1 / ((n : ℝ) + 1)) 1, fun _ => isClosed_Icc, ?_⟩
  show ¬ IsClosed (⋃ n : ℕ, Icc (1 / ((n : ℝ) + 1)) 1)
  have hUnion : (⋃ n : ℕ, Icc (1 / ((n : ℝ) + 1)) 1) = Ioc (0 : ℝ) 1 := by
    ext x
    simp only [mem_iUnion, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨n, hn1, hn2⟩
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
        have h := Nat.cast_nonneg (α := ℝ) n; positivity
      exact ⟨lt_of_lt_of_le hpos hn1, hn2⟩
    · rintro ⟨hx0, hx1⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / x)
      refine ⟨n, ?_, hx1⟩
      rw [div_le_iff₀ (by have h := Nat.cast_nonneg (α := ℝ) n; positivity)]
      rw [div_lt_iff₀ hx0] at hn
      nlinarith
  rw [hUnion]
  intro h
  have hcl := h.closure_eq
  rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)] at hcl
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl 0, by norm_num⟩
  rw [hcl] at h0
  exact absurd h0.1 (lt_irrefl 0)
