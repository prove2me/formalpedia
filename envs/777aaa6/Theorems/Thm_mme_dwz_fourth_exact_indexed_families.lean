-- Prove2me | Theorems.Thm_mme_dwz_fourth_exact_indexed_families
-- name    : mme_dwz_fourth_exact_indexed_families
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T21:27:08.532914+00:00
-- url     : https://prove2.me/theorems/a558891e-557c-4834-a782-db9f7eae1dbe
-- title:
--   Complete indexed fourth-level families with exact target and ambient-star counts
-- statement:
--   Let $C=\{0,\ldots,k-1\}$ and let $\sigma$ be a bijection from $C$ to the supported fourth-level addresses
--   $$
--   \mathcal S=\{s\in\{0,\ldots,8\}^3:s_0+s_1+s_2=8\}.
--   $$
--   Let $n_c$ be arbitrary nonnegative integers with $\sum_c n_c=N$. Write $s_i(c)=\sigma(c)_i$ and define the exact marginal counts
--   $$
--   M_i(g)=\sum_{c:s_i(c)=g}n_c.
--   $$
--   Outside $0\le g\le8$, these marginal counts are zero.
--
--   There are a natural number $R$, an injective family of words $w_a:\{0,\ldots,N-1\}\to C$ indexed by $a\in\{0,\ldots,R-1\}$, and a nonempty target set $T$ of indices with the following properties.
--
--   1. The ambient index set is all of $\{0,\ldots,R-1\}$. Its coarse addresses $A_a(i,t)=s_i(w_a(t))$ are distinct, supported, and have marginal counts $M_i(g)$. Conversely, every supported natural-number address with these three marginals equals exactly one $A_a$.
--
--   2. An index belongs to $T$ if and only if each label $c$ occurs exactly $n_c$ times in $w_a$. Every word with these exact label counts occurs in $T$, and
--   $$
--   |T|=\frac{N!}{\prod_{c\in C}n_c!}>0.
--   $$
--   For each $a\in T$, there is an actual bijection
--   $$
--   \pi_a:\{0,\ldots,N-1\}\simeq\coprod_{c\in C}\{0,\ldots,n_c-1\},
--   \qquad w_a(\pi_a^{-1}(c,r))=c.
--   $$
--
--   3. Let $\mathcal H_N(M)$ be the set of all tables $h:\mathcal S\to\{0,\ldots,N\}$ satisfying $\sum_{s:s_i=g}h(s)=M_i(g)$ for every mode $i$ and grade $g$. For every ambient index $a$ and every mode $i$, the exact full ambient star size is
--   $$
--   \#\{b:A_b(i,\cdot)=A_a(i,\cdot)\}
--   =\sum_{h\in\mathcal H_N(M)}
--   \prod_{g=0}^{8}\frac{M_i(g)!}{\prod_{s\in\mathcal S:s_i=g}h(s)!}.
--   $$
--
--   Thus the target family has one prescribed joint type, whereas the ambient family includes every joint type with the same marginals. All counts, existence assertions, and position bijections are conclusions, including when $N=0$ or some $n_c=0$. This is a finite combinatorial interface for the fourth-power hash argument; it asserts neither tensor extraction nor a split-profile compatibility estimate or an entropy ceiling.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S3.SS7 , Section 3.7, Definition 3.5 (joint and marginal component distributions), and Section 3.10 (full marginal ambient family and good joint-type triples). Denominator-cleared finite construction derived from these definitions; exact star count reuses public theorem mme_dwz_fourth_ambient_mode_star_card (3960a3ed-ff1d-43df-a7b7-388448f70f0a). This bundled interface is not attributed as a verbatim numbered statement of the paper.

import Definitions.Def_mme_dwz_simultaneous_CW_projection_data
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

open BigOperators MME.DWZSimultaneous
open scoped Classical
set_option autoImplicit false

theorem mme_dwz_fourth_exact_indexed_families (N k : ℕ)
    (sigma : Fin k ≃ {s : Fin 3 → Fin 9 // (∑ i, (s i).val) = 8})
    (n : Fin k → ℕ) (hn : ∑ c, n c = N) :
    let shape : Fin k → Fin 3 → ℕ := fun c i ↦ ((sigma c).val i).val
    let marginal : Fin 3 → ℕ → ℕ :=
      fun i g ↦ ∑ c : {c : Fin k // shape c i = g}, n c.val
    let M := fun i (g : Fin 9) ↦ marginal i g.val
    let Cell := {s : Fin 3 → Fin 9 // (∑ i, (s i).val) = 8}
    let admissible : Finset (Cell → Fin (N + 1)) := Finset.univ.filter (fun h ↦
      ∀ i : Fin 3, ∀ g : Fin 9,
        (∑ s : {s : Cell // s.val i = g}, (h s.val).val) = M i g)
    ∃ (R : ℕ) (component : Fin R → Fin N → Fin k) (targets : Finset (Fin R)),
      Function.Injective component ∧
      Function.Injective (owner component shape) ∧
      (∀ a, SameMarginal marginal (owner component shape a)) ∧
      (∀ a, Supported 8 (owner component shape a)) ∧
      (∀ a : CoarseAddress N, Supported 8 a → SameMarginal marginal a →
        ∃ b, owner component shape b = a) ∧
      (∀ a, a ∈ targets ↔
        ∀ c, Fintype.card {t : Fin N // component a t = c} = n c) ∧
      (∀ w : Fin N → Fin k, (∀ c, Fintype.card {t : Fin N // w t = c} = n c) →
        ∃ a ∈ targets, component a = w) ∧
      targets.card = N.factorial / ∏ c, (n c).factorial ∧
      targets.Nonempty ∧
      (∃ positions : ∀ a : Fin R, a ∈ targets → (Fin N ≃ Σ c, Fin (n c)),
        ∀ a ha c r, component a ((positions a ha).symm ⟨c, r⟩) = c) ∧
      (∀ (mode : Fin 3) (a : Fin R),
        (Finset.univ.filter (fun b ↦
          owner component shape b mode = owner component shape a mode)).card =
          ∑ h ∈ admissible, ∏ g : Fin 9, (M mode g).factorial /
            ∏ s : {s : Cell // s.val mode = g}, ((h s.val).val).factorial) := by sorry
