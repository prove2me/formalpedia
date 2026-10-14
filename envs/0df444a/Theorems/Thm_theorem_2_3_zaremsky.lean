-- Prove2me | Theorems.Thm_theorem_2_3_zaremsky
-- name    : theorem_2_3_zaremsky
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-12T18:39:58.077325+00:00
-- url     : https://prove2.me/theorems/9c10f153-3ad5-48d2-8bd5-cabd2046c28a
-- title:
--   Theorem 2.3 (Zaremsky's finite-presentation criterion)
-- statement:
--   Suppose a finitely presented group $\Lambda$ acts faithfully on a nonempty countable set $X$. If every point stabilizer is finitely generated, and there are finitely many $\Lambda$-orbits on the unordered two-element subsets of $X$ (i.e. on non-diagonal elements of the symmetric square $\mathrm{Sym}^2(X)$), then $\Lambda$ embeds into a nontrivial finitely presented simple group.
--
--   This is Zaremsky's finite-presentation theorem for the twisted Brin–Thompson construction of Belk and Zaremsky, which produces the simple overgroup and the embedding explicitly from such an action; finite presentation of the overgroup is due to Zaremsky's strengthening of the original Belk–Zaremsky finite-presentation criterion. It is cited here in exactly the form the Boone–Higman envelopes preprint applies it (its Theorem 2.3), not in its most general stated form.
--
--   **Formalization Note** "Finitely many orbits on unordered pairs" is formalized as a finite set of representative pairs (elements of `Sym2 X`) whose $\Lambda$-orbits, under the induced action `Sym2.map (γ • ·)`, cover every pair of distinct points. The conclusion reuses this mission's own `EmbedsInFinitelyPresentedSimpleGroup`, whose existential already forces the target group nontrivial via `IsSimpleGroup`.
-- source:
--   M. C. B. Zaremsky, *Finite presentability of twisted Brin–Thompson groups*, Proc. Roy. Soc. Edinburgh Sect. A (2024), https://doi.org/10.1017/prm.2024.131, Theorem A and Corollary B, cited as Theorem 2.3 of OpenAI, *Finite algebraic envelopes and the Boone–Higman conjecture*, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf, p. 5, in the precise form that preprint applies it.

import Mathlib
import Definitions.Def_BooneHigman

universe u

theorem theorem_2_3_zaremsky {Λ : Type u} [Group Λ] [Group.IsFinitelyPresented Λ]
    {X : Type u} [Nonempty X] [Countable X] [MulAction Λ X] [FaithfulSMul Λ X]
    (hstab_fg : ∀ x : X, Group.FG (MulAction.stabilizer Λ x))
    (horbits : ∃ reps : Finset (Sym2 X), ∀ p : Sym2 X, ¬p.IsDiag →
      ∃ q ∈ reps, ∃ γ : Λ, Sym2.map (fun x => γ • x) q = p) :
    OAI.FiniteAlgebraicEnvelopes.EmbedsInFinitelyPresentedSimpleGroup Λ := by
  sorry
