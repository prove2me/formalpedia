-- Prove2me | Theorems.Thm_YangMills_os_positivity_cauchy_schwarz
-- name    : YangMills.os_positivity_cauchy_schwarz
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T12:50:29.842168+00:00
-- url     : https://prove2.me/theorems/c9946879-8d09-4ab4-8370-3233312d89e0
-- title:
--   Cauchy–Schwarz inequality for the Osterwalder–Schrader form
-- statement:
--   **The Cauchy–Schwarz inequality for the Osterwalder–Schrader inner product.**
--
--   Let $(S_n)$ satisfy the Osterwalder–Schrader axioms and write $\theta$ for Euclidean time
--   reflection $(x^0,\vec x)\mapsto(-x^0,\vec x)$. For test functions $f,g$ supported in
--   $\{x^0>0\}$, reflection positivity makes
--   $$\langle f,g\rangle_{\mathrm{OS}}:=S_2(f\circ\theta,\ g)$$
--   a positive semi-definite Hermitian form on the positive-time test functions. Consequently
--
--   $$\bigl|S_2(f\circ\theta,g)\bigr|\ \le\ \sqrt{\operatorname{Re}S_2(f\circ\theta,f)}\ \cdot\
--   \sqrt{\operatorname{Re}S_2(g\circ\theta,g)} .$$
--
--   This is the first step of the Osterwalder–Schrader reconstruction: the form
--   $\langle\cdot,\cdot\rangle_{\mathrm{OS}}$ descends to an inner product on the quotient by its
--   null space, whose completion is the physical Hilbert space, and the Cauchy–Schwarz inequality is
--   what makes that quotient and the subsequent operator bounds meaningful. It is stated here as an
--   entry point into the mission: it uses only the reflection positivity axiom.
-- source:
--   K. Osterwalder and R. Schrader, Axioms for Euclidean Green's functions II, Comm. Math. Phys. 42 (1975) 281-305, Section 2 (the OS inner product); J. Glimm and A. Jaffe, Quantum Physics: A Functional Integral Point of View, 2nd ed., Springer 1987, Chapter 6.1.

import Definitions.Def_YangMills_Wilson_lattice

open MeasureTheory Filter Topology Finset

namespace YangMills

theorem os_positivity_cauchy_schwarz (Q : OSTheory) (f g fθ gθ : TestFn)
    (hf : PosTime f) (hg : PosTime g)
    (hfθ : ∀ x : Spacetime, fθ x = f (timeReflect x))
    (hgθ : ∀ x : Spacetime, gθ x = g (timeReflect x)) :
    ‖Q.S 2 ![fθ, g]‖ ≤ Real.sqrt (Q.S 2 ![fθ, f]).re * Real.sqrt (Q.S 2 ![gθ, g]).re := by
  sorry

end YangMills
