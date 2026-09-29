-- Prove2me | Definitions.Def_mme_strassen_preorder
-- name    : mme_strassen_preorder
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-29T15:29:59.596724+00:00
-- url     : https://prove2.me/theorems/6d211b5e-48db-4f6d-aef2-ac07e2990a6a
-- statement:
--   **Abstract Strassen preorders, rank, and asymptotic rank.**
--
--   The lightweight abstract backbone of the asymptotic-spectrum theory, following Wigderson–Zuiddam (*Asymptotic spectra: theory, applications and extensions*, Def. 2.3–2.8). Kept deliberately small — only structures and the two rank definitions live here; properties are proved in downstream files.
--
--   **Structures.**
--   - `SemiringPreorder R` — a preorder on a `CommSemiring` compatible with $+$ and $\cdot$: $a \leq b \Rightarrow a + c \leq b + c$ and $a \cdot c \leq b \cdot c$, plus $0 \leq a$ everywhere.
--   - `StrassenPreorder R` — extends `SemiringPreorder` with the **natural-number order embedding** axiom: for $n, m : \mathbb{N}$ (cast into $R$ via repeated $1$-addition), $n \leq_R m \iff n \leq m$. This is the abstraction of the "$n$-element diagonal restricts to $m$-element diagonal iff $n \leq m$" property that powers integer rank.
--
--   **Rank functions.** For a Strassen preorder $P$ on $R$:
--   - $\mathrm{rank}_P(a) = \inf\{ n \in \mathbb{N} : a \leq_P n \}$ — the least natural number dominating $a$.
--   - $\mathrm{asymptoticRank}_P(a) = \inf_{n} \mathrm{rank}_P(a^{n+1})^{1/(n+1)}$ — Fekete's amortized form.
--
--   **Reusability.** The same `rank` / `asymptoticRank` is later instantiated on the tensor quotient (`Def_mme_tensor_quotient`) to recover ordinary and asymptotic tensor rank; every general fact (sub-multiplicativity, Fekete limits, duality, fractional rank, spectrum) is proved once on `StrassenPreorder` rather than per-instance.

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Strassen preorders, rank, and asymptotic rank

The abstract backbone of the asymptotic-spectrum theory, following
Wigderson–Zuiddam (*Asymptotic spectra: theory, applications and extensions*),
Definitions 2.3–2.8.

The point of the abstraction is reuse: the same `rank` / `asymptoticRank` will be
instantiated on the tensor semiring to recover ordinary and asymptotic tensor rank,
and every general fact (sub-multiplicativity, Fekete limits, duality) is proved once
here rather than per-instance. Kept deliberately lightweight — only structures and
the two rank definitions live here; their properties are separate theorems. -/

universe u

namespace MME

variable {R : Type u}

/-- A preorder on a commutative semiring compatible with `+` and `*`
(Wigderson–Zuiddam, Def. 2.3): reductions compose under both operations, and every
element is non-negative. -/
structure SemiringPreorder (R : Type u) [CommSemiring R] extends Preorder R where
  add_right : ∀ a b, le a b → ∀ c, le (a + c) (b + c)
  mul_right : ∀ a b, le a b → ∀ c, le (a * c) (b * c)
  zero_le : ∀ a : R, le 0 a

/-- A Strassen preorder (Wigderson–Zuiddam, Def. 2.4): a semiring preorder in which

* the positive integers embed in their natural order (`nat_order_embedding`),
* every element is bounded below by `1` once nonzero (`lower_archimedean`),
* every element is bounded above by some integer (`upper_archimedean`, the strong
  Archimedean property).

These are exactly the conditions making `rank` and `asymptoticRank` well-defined and
finite. -/
structure StrassenPreorder (R : Type u) [CommSemiring R] extends SemiringPreorder R where
  nat_order_embedding : ∀ n m : ℕ, le (n : R) (m : R) ↔ n ≤ m
  lower_archimedean : ∀ a : R, a = 0 ∨ le 1 a
  upper_archimedean : ∀ a : R, ∃ n : ℕ, le a (n : R)

namespace StrassenPreorder

variable [CommSemiring R] (P : StrassenPreorder R)

/-- **Rank** (Wigderson–Zuiddam, Def. 2.5): the least integer `n` with `a ≤ n`,
the "cost" of `a` measured in copies of the unit. Finite by `upper_archimedean`. -/
noncomputable def rank (a : R) : ℕ := sInf {n : ℕ | P.le a (n : R)}

/-- **Asymptotic rank** (Wigderson–Zuiddam, Def. 2.8): the amortized cost
`inf_n rank(aⁿ)^(1/n)`. Real-valued; by Fekete's lemma the infimum is a limit. -/
noncomputable def asymptoticRank (a : R) : ℝ :=
  ⨅ n : ℕ, (P.rank (a ^ (n + 1)) : ℝ) ^ ((1 : ℝ) / (n + 1))

/-- A Strassen preorder is **total** if any two elements are comparable. Total (and
closed) preorders are exactly the ones whose fractional rank `ρ` is an asymptotic-spectrum
point. -/
def IsTotal (P : StrassenPreorder R) : Prop :=
  ∀ a b : R, P.le a b ∨ P.le b a

end StrassenPreorder

end MME


