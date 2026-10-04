-- Prove2me | Theorems.Thm_ZetaNine_irrational_of_small_nonzero_integer_forms
-- name    : ZetaNine.irrational_of_small_nonzero_integer_forms
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T02:42:27.715979+00:00
-- url     : https://prove2.me/theorems/c1147ec6-b702-4ce3-86a6-04aaf358e544
-- title:
--   One-form irrationality criterion
-- statement:
--   ## One-form irrationality criterion
--
--   Let $x \in \mathbb{R}$. Suppose that for **every** $\varepsilon>0$ there are integers
--   $b,a \in \mathbb{Z}$ such that the integer form $b+ax$ is **nonzero** and
--
--   $$0<|b+ax|<\varepsilon .$$
--
--   Then $x$ is irrational.
--
--   **Why.** Write a supposed rational value as $x=p/q$ with $q\neq 0$. Applying the
--   hypothesis with $\varepsilon=1/|q|$ produces $(b,a)$ with
--
--   $$0<|b+a\,p/q|<1/|q| .$$
--
--   Multiplying by $|q|$ gives $0<|bq+ap|<1$, but $bq+ap$ is an integer, and the only
--   integer of absolute value $<1$ is $0$. Hence $bq+ap=0$, that is $b+a\,p/q=0$,
--   contradicting $b+a\,p/q\neq 0$. Therefore $x\notin\mathbb{Q}$.
--
--   **Scope.** This is the *criterion* half of local node **TP** ("positive one-form
--   bridge"): it converts a supply of small nonzero integer forms in $1$ and $x$ into
--   irrationality of $x$, with no independence hypothesis and no reference to the
--   $\zeta(9)$ construction. On the actual construction the missing input is the sign
--   certificate that makes the form nonzero: the note-proved comparison is that a
--   nonzero quartic with all five Taylor coefficients at $u_0$ of one weak sign has a
--   strictly nonzero complete weighted sum, so the corresponding integer form is
--   nonzero. Neither the sign certificate for the concrete construction nor the
--   existence of the forms is claimed here. The theorem is stated for an arbitrary real
--   $x$ and proved outright.
-- source:
--   Local zeta9 research note, roadmap/research/full-lattice-sign-next.md and roadmap/research/moving-short-sign-next.md, node TP, 2026-09-25

import Mathlib

namespace ZetaNine

theorem irrational_of_small_nonzero_integer_forms (x : ℝ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ b a : ℤ,
        (b : ℝ) + (a : ℝ) * x ≠ 0 ∧
        |(b : ℝ) + (a : ℝ) * x| < ε) :
    Irrational x := by sorry

end ZetaNine
