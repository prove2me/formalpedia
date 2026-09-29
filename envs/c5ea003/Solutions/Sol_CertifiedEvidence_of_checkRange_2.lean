-- Prove2me | solution 2 for CertifiedEvidence.of_checkRange
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T09:37:15.605675+00:00
-- url     : https://prove2.me/submissions/e7ecaf8e-ba30-4940-b88a-b169230aa959

/-
# `CertifiedEvidence.of_checkRange`
Target `c219f37a` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle screened CLEAN. Gift check: **SAFE** (graph: 12 nodes, 0 sketch-edges).

BINDERS — note the unusual interleaving, copied verbatim from the platform record: `{k : ℕ}` comes
AFTER the hypothesis `(h : checkRange p lo hi = true)`, not with `{lo hi}`. History is `CE,…` so no
WA has ever published an expected type for this target; the generated gate is the sole authority.

WHAT THE BUNDLE ACTUALLY PROVIDES. Core declares exactly three things — `checkFrom`, `checkRange`,
`firstFail`. Its doc comment advertises `checkRange_eq_true_iff` as "the soundness *and* completeness
bridge", but skeleton subtraction removed it and it is not an Open target either. So there is no
`checkRange`-level lemma to lean on, and `checkFrom_eq_true_iff` (which I have submitted separately)
cannot be imported from `Theorems/` without forcing the reduction path and an axiom audit.
It is therefore RE-DERIVED INLINE below, exactly as `H_pos_of_ne` re-derived `self_mem_img`.

THE BRIDGE IS DEFINITIONAL: `checkRange p lo hi` unfolds to `checkFrom p lo (hi + 1 - lo)`, so the
hypothesis `h` retypes with no rewriting at all. Instantiating the keystone at `n := hi + 1 - lo`
gives `∀ j, lo ≤ j → j < lo + (hi + 1 - lo) → p j = true`, and the remaining side condition
`k < lo + (hi + 1 - lo)` is linear: from `lo ≤ k ≤ hi` we get `lo ≤ hi`, so the truncated subtraction
is exact and the bound is `hi + 1`. `omega` handles truncated subtraction natively.
-/
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core

set_option autoImplicit false
set_option maxHeartbeats 400000

open CertifiedEvidence

open CertifiedEvidence in
/-- **The target, verbatim.** -/
theorem solution {p : ℕ → Bool} {lo hi : ℕ} (h : checkRange p lo hi = true)
    {k : ℕ} (h1 : lo ≤ k) (h2 : k ≤ hi) : p k = true := by
  -- the keystone, re-derived inline (see header: importing it would force the reduction path)
  have key : ∀ (n lo : ℕ), checkFrom p lo n = true ↔ ∀ j, lo ≤ j → j < lo + n → p j = true := by
    intro n
    induction n with
    | zero =>
        intro lo
        constructor
        · intro _ j hj1 hj2
          exfalso; omega
        · intro _
          rfl
    | succ n ih =>
        intro lo
        simp only [checkFrom, Bool.and_eq_true, ih (lo + 1)]
        constructor
        · rintro ⟨hlo, hrest⟩ j hj1 hj2
          rcases Nat.eq_or_lt_of_le hj1 with hq | hq
          · subst hq; exact hlo
          · exact hrest j (by omega) (by omega)
        · intro hall
          exact ⟨hall lo le_rfl (by omega), fun j hj1 hj2 => hall j (by omega) (by omega)⟩
  -- `checkRange p lo hi` IS `checkFrom p lo (hi + 1 - lo)` definitionally, so `h` retypes as-is
  have h' : checkFrom p lo (hi + 1 - lo) = true := h
  exact (key (hi + 1 - lo) lo).mp h' k h1 (by omega)
