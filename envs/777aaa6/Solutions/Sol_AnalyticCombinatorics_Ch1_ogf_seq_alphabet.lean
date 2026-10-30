-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.ogf_seq_alphabet
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:34:26.704183+00:00
-- url     : https://prove2.me/submissions/ab0afd54-0d51-418f-b7e4-7c7aadd02514

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_ProductPower
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_SequenceInverse
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.1 — Combinatorial classes and ordinary generating functions

A faithful encoding of Flajolet & Sedgewick, *Analytic Combinatorics*, Part A,
Chapter I, §I.1. A combinatorial class is a set of objects equipped with a size
function such that only finitely many objects have any given size. We encode it
as a graded family of finite types `Obj : ℕ → Type`, where `Obj n` is the set of
objects of size `n`. Its counting sequence is `Aₙ = #(Obj n)`, and its *ordinary
generating function* (OGF) is `A(z) = ∑ₙ Aₙ zⁿ`, here a formal power series over
`ℚ`.

This file defines the OGF, the `CombClass` structure, and the three primitive
classes (empty `∅`, neutral `ε`, atom `Z`) with their counting sequences and
generating functions `ε(z) = 1`, `Z(z) = z`. The admissible constructions (sum,
product, sequence) and their transfer theorems live in sibling files.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma coeff_ogfSeq (a : ℕ → ℕ) (n : ℕ) : coeff n (ogfSeq a) = (a n : ℚ) := by
  rw [ogfSeq, coeff_mk]

attribute [instance] CombClass.finObj

@[simp] lemma CombClass.coeff_ogf (C : CombClass) (n : ℕ) :
    coeff n C.ogf = (C.counts n : ℚ) := by
  rw [CombClass.ogf, coeff_ogfSeq]

end AnalyticCombinatorics.Ch1

/-!
# Ch1 §I.2 / §I.3 — The sequence construction and integer compositions

Flajolet & Sedgewick, Part A, Chapter I. The sequence construction `SEQ(C)` forms
all finite sequences `(γ₁, …, γₘ)` of `C`-objects, with size the sum of the
component sizes. For this to give a (finite) combinatorial class one needs `C` to
have no object of size `0` (F&S's standing side-condition); the positive
component sizes of a size-`n` sequence then form a *composition* of `n`, so we
model `SEQ(C)` over Mathlib's `Composition n`.

This file proves, at the level of counting sequences, the genuine combinatorial
content:

* `counts_seq` — `(SEQ C)ₙ = ∑_{compositions c of n} ∏ᵢ C_{cᵢ}`.
* `counts_seq_posInt` — **integer compositions are sequences of positive
  integers** (F&S §I.3): `(SEQ ℙ)ₙ = #(Composition n) = 2^{n-1}`.

The closed-form generating function of compositions lives in `Compositions.lean`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- Counting sequence of `SEQ(C)`: `(SEQ C)ₙ = ∑_{compositions c of n} ∏ᵢ C_{cᵢ}`.
The genuine combinatorial content, from `Fintype.card_sigma` and
`Fintype.card_pi`. -/
lemma CombClass.counts_seq (C : CombClass) (n : ℕ) :
    C.seq.counts n
      = ∑ c : Composition n, ∏ i : Fin c.length, C.counts (c.blocksFun i) := by
  change Fintype.card (Σ c : Composition n, ∀ i : Fin c.length, C.Obj (c.blocksFun i)) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.card_pi]
  rfl

end AnalyticCombinatorics.Ch1

/-!
# Ch1 §I.2–I.3 — Cartesian powers and words over a finite alphabet

Flajolet & Sedgewick, Part A, Chapter I. Iterating the product construction gives
the `k`-fold Cartesian power `C^k = C × C × ⋯ × C`, with OGF `C(z)^k` (an immediate
induction from the binary product rule `ogf_prod`). As the standard application,
words of length `k` over an alphabet of `a` letters form `(a·Z)^k`, with OGF
`(a z)^k` (so there are `a^k` of them), recovering F&S §I.3.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma CombClass.counts_alphabet (a n : ℕ) :
    (CombClass.alphabet a).counts n = if n = 1 then a else 0 :=
  Fintype.card_fin _

/-- The OGF of an `a`-letter alphabet is `a·z`. -/
theorem CombClass.ogf_alphabet (a : ℕ) :
    (CombClass.alphabet a).ogf = (a : ℕ) • X := by
  ext n
  rw [CombClass.coeff_ogf, CombClass.counts_alphabet, map_nsmul, coeff_X]
  by_cases h : n = 1 <;> simp [h]

end AnalyticCombinatorics.Ch1

/-!
# Ch1 §I.2 — The sequence construction: `SEQ(C)(z) = 1/(1 - C(z))`

Flajolet & Sedgewick, Part A, Chapter I, §I.2, the sequence construction, for a
general class `C` with no object of size `0` (`C.counts 0 = 0`). A sequence
decomposes as `SEQ(C) = ε + C × SEQ(C)` (empty, or first component × rest), so the
counting sequence satisfies a convolution recursion and the OGF satisfies the
functional equation `S(z) = 1 + C(z)·S(z)`, hence

  **`(seq C).ogf · (1 - C.ogf) = 1`**, i.e. `SEQ(C)(z) = 1/(1 - C(z))`.

The combinatorial core is the first-part decomposition of compositions, built from
Mathlib's `Composition.append`/`single`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

variable {C : CombClass}

lemma consSeq_blocks (n : ℕ) (k : Fin (n + 1)) (c : Composition (n - (k : ℕ))) :
    (consSeq n k c).blocks = ((k : ℕ) + 1) :: c.blocks := by
  simp [consSeq, Composition.single_blocks]

lemma prod_consSeq (n : ℕ) (k : Fin (n + 1)) (c : Composition (n - (k : ℕ))) :
    ((consSeq n k c).blocks.map C.counts).prod
      = C.counts ((k : ℕ) + 1) * (c.blocks.map C.counts).prod := by
  rw [consSeq_blocks, List.map_cons, List.prod_cons]

/-- `counts_seq` rewritten as a sum of products over the blocks list. -/
lemma counts_seq_eq_listProd (m : ℕ) :
    C.seq.counts m = ∑ c : Composition m, (c.blocks.map C.counts).prod := by
  rw [C.counts_seq]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Composition.ofFn_blocksFun c, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply]

lemma consSeq_bijective (n : ℕ) :
    Function.Bijective
      (fun p : Σ k : Fin (n + 1), Composition (n - (k : ℕ)) => consSeq n p.1 p.2) := by
  constructor
  · rintro ⟨k, cp⟩ ⟨k', cq⟩ hpq
    simp only at hpq
    have hb : ((k : ℕ) + 1) :: cp.blocks = ((k' : ℕ) + 1) :: cq.blocks := by
      rw [← consSeq_blocks, ← consSeq_blocks, hpq]
    rw [List.cons.injEq] at hb
    obtain ⟨hk, hblocks⟩ := hb
    have hkk : k = k' := Fin.ext (by omega)
    subst hkk
    have : cp = cq := Composition.ext hblocks
    subst this
    rfl
  · intro c
    have hne : c.blocks ≠ [] := by rw [Ne, Composition.blocks_eq_nil]; omega
    obtain ⟨b, rest, hbr⟩ := List.exists_cons_of_ne_nil hne
    have hb1 : 1 ≤ b := c.one_le_blocks (by rw [hbr]; exact List.mem_cons_self ..)
    have hsum : b + rest.sum = n + 1 := by
      have hs := c.blocks_sum; rw [hbr, List.sum_cons] at hs; omega
    refine ⟨⟨⟨b - 1, by omega⟩, ⟨rest, ?_, ?_⟩⟩, ?_⟩
    · intro i hi
      exact c.blocks_pos (by rw [hbr]; exact List.mem_cons_of_mem _ hi)
    · change rest.sum = n - (b - 1); omega
    · apply Composition.ext
      rw [consSeq_blocks]
      change (b - 1 + 1) :: rest = c.blocks
      rw [Nat.sub_add_cancel hb1]
      exact hbr.symm

/-- The convolution recursion: a nonempty sequence is a first component (size
`k+1`) followed by a sequence of the remaining size. -/
lemma counts_seq_succ (n : ℕ) :
    C.seq.counts (n + 1)
      = ∑ k : Fin (n + 1), C.counts ((k : ℕ) + 1) * C.seq.counts (n - (k : ℕ)) := by
  rw [counts_seq_eq_listProd,
    ← Fintype.sum_bijective _ (consSeq_bijective n)
        (fun p => ((consSeq n p.1 p.2).blocks.map C.counts).prod)
        (fun c => (c.blocks.map C.counts).prod) (fun _ => rfl),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp_rw [prod_consSeq]
  rw [← Finset.mul_sum, ← counts_seq_eq_listProd]

lemma counts_seq_zero : C.seq.counts 0 = 1 := by
  rw [counts_seq_eq_listProd]
  have h : ∀ c : Composition 0, (c.blocks.map C.counts).prod = 1 := by
    intro c
    have hnil : c.blocks = [] := by simp
    simp [hnil]
  simp [h, Finset.card_univ, composition_card]

private lemma constantCoeff_ogf (hC0 : C.counts 0 = 0) :
    constantCoeff (R := ℚ) C.ogf = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_ogf, hC0, Nat.cast_zero]

/-- **The sequence functional equation** (F&S §I.2): `S(z) = 1 + C(z)·S(z)` for a
class `C` with `C₀ = ∅`. -/
theorem CombClass.ogf_seq_functional_eq (hC0 : C.counts 0 = 0) :
    C.seq.ogf = 1 + C.ogf * C.seq.ogf := by
  ext m
  rcases m with _ | n
  · rw [CombClass.coeff_ogf, counts_seq_zero]
    simp [coeff_zero_eq_constantCoeff, constantCoeff_ogf hC0]
  · rw [CombClass.coeff_ogf, counts_seq_succ, map_add, coeff_one,
      if_neg (Nat.succ_ne_zero n), zero_add, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
    push_cast
    rw [CombClass.coeff_ogf, hC0,
      Fin.sum_univ_eq_sum_range
        (fun k => (C.counts (k + 1) : ℚ) * (C.seq.counts (n - k) : ℚ)) (n + 1)]
    simp [CombClass.coeff_ogf]

/-- **The sequence construction** (F&S Theorem I.1): for a class `C` with `C₀ = ∅`,
`(seq C)(z)·(1 - C(z)) = 1`, i.e. `SEQ(C)(z) = 1/(1 - C(z))`. -/
theorem CombClass.ogf_seq_mul (hC0 : C.counts 0 = 0) :
    C.seq.ogf * (1 - C.ogf) = 1 := by
  set_option backward.isDefEq.respectTransparency false in
    linear_combination CombClass.ogf_seq_functional_eq hC0

end AnalyticCombinatorics.Ch1

/-!
# Ch1 §I.3 — Applications of the sequence construction

Flajolet & Sedgewick, Part A, Chapter I, §I.3, applying the general transfer
`SEQ(C)(z) = 1/(1 - C(z))` (`ogf_seq_mul`):

* `counts_seq_alphabet` / `ogf_seq_alphabet` — **words over a finite alphabet**:
  `SEQ` of an `a`-letter alphabet enumerates all words; there are `a^n` of length
  `n`, with OGF `1/(1 - a z)`.
* `ogf_seq_posInt` — **compositions revisited**: the special case `C = ℙ`
  recovers `(seq ℙ)(z)·(1 - ℙ(z)) = 1` as an instance of the general theorem
  (cf. the bespoke proof in `SeqFormula.lean`).
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

end AnalyticCombinatorics.Ch1

open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open PowerSeries
theorem solution (a : ℕ) :
    (CombClass.alphabet a).seq.ogf * (1 - (a : ℕ) • X) = 1 := by
  have h := CombClass.ogf_seq_mul (C := CombClass.alphabet a)
    (by simp [CombClass.counts_alphabet])
  rwa [CombClass.ogf_alphabet] at h
