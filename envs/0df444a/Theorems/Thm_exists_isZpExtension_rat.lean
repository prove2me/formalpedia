-- Prove2me | Theorems.Thm_exists_isZpExtension_rat
-- name    : exists_isZpExtension_rat
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:23:59.728011+00:00
-- url     : https://prove2.me/theorems/c088ca9f-c793-4de9-b87c-6750388c6340
-- title:
--   Existence of the cyclotomic $\mathbb Z_p$-extension of $\mathbb Q$
-- statement:
--   Let $p$ be an odd prime and $\overline{\mathbb Q}$ an algebraic closure of $\mathbb Q$. There is a subfield $\mathbb Q_\infty\subseteq\overline{\mathbb Q}$ such that $\mathbb Q_\infty/\mathbb Q$ is a $\mathbb Z_p$-extension, i.e. $\mathbb Q_\infty/\mathbb Q$ is Galois and
--   $$\mathrm{Gal}(\mathbb Q_\infty/\mathbb Q)\;\cong\;\mathbb Z_p$$
--   as topological groups (Krull topology on the left).
--
--   Concretely, $\mathbb Q_\infty$ is the unique subfield of $\mathbb Q(\mu_{p^\infty})$ fixed by the torsion subgroup $\mu_{p-1}\subset\mathbb Z_p^\times\cong\mathrm{Gal}(\mathbb Q(\mu_{p^\infty})/\mathbb Q)$: the cyclotomic $\mathbb Z_p$-extension of $\mathbb Q$. Composing with any number field $K$ it yields the cyclotomic $\mathbb Z_p$-extension of $K$, the basic object of Iwasawa theory.
--
--   **Formalization Note** "$\mathbb Z_p$-extension" is the platform definition `IsZpExtension` (Galois, with Galois group topologically isomorphic to `Multiplicative ℤ_[p]`).
-- source:
--   L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, §13.1 (the cyclotomic Z_p-extension of Q, constructed from Gal(Q(μ_{p^∞})/Q) ≅ Z_p^× ≅ μ_{p-1} × (1+pZ_p)); K. Iwasawa, On Γ-extensions of algebraic number fields, Bull. AMS 65 (1959), 183–226.

import Definitions.Def_ZpExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

theorem exists_isZpExtension_rat (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), IsZpExtension p ℚ L := by sorry
