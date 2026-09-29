-- Prove2me | Theorems.Thm_mme_recursive_yz_compatible_competitor_bound
-- name    : mme_recursive_yz_compatible_competitor_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-12T10:20:21.82954+00:00
-- url     : https://prove2.me/theorems/0b920e9d-89b1-492a-b6f0-5fdb208aeff4
-- title:
--   Recursive Y/Z filtering: finite bound on compatible competitors
-- statement:
--   Fix the prescribed recursive split counts, one mode $i$, and one coarse word $y$ in that mode. Let $T_y$ be the exact-profile target addresses whose mode-$i$ word is $y$. Fix joint full-parent fine-word counts $\eta$ within the coarse-word cells, and let $F_\eta(y)$ be their type class. The full parent word is an ordered pair of child words, so both halves remain coupled.
--
--   For a fine word $f\in F_\eta(y)$, let $C(f)$ be the number of addresses in $T_y$ compatible with $f$. If the prescribed fine cell counts $\mu$ sum to $m_r(a)+m_r(\bar a)$, then
--
--   $$C(f)\,|F_\eta(y)|\le |T_y|\,Q(\mu),$$
--
--   where $Q(\mu)$ is the exact boundary/interior multinomial compatibility count. The boundary and grouping may be chosen as the physical Y filter ($k'=0$, grouped by Y grade) or the physical Z filter ($i'=0$ or $j'=0$, grouped by Z grade).
--
--   This is the finite double-counting bound underlying Claims 6.18 and 6.20. It retains the full joint parent-type denominator. No entropy asymptotics, hash survival estimate, or tensor extraction is asserted.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Claims 6.18--6.20; https://arxiv.org/html/2404.16349v2#S6.SS5. Exact finite-count generalization of the conditional symmetry/double-counting argument.

import Definitions.Def_mme_recursive_yz_physical_words
import Definitions.Def_mme_recursive_x_hash_families
open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false

theorem mme_recursive_yz_compatible_competitor_bound {half R : ℕ} {W G : Type*} [Fintype W] [Fintype G]
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (i : Fin 3) (y : ∀ r, Fin (n r) → Fin (half + 1))
    (eta : Fin R → Fin (half + 1) → (Fin 2 → W) → ℕ)
    (boundary : Cell half R parent → Prop) (group : Cell half R parent → G)
    (mu : Cell half R parent → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (f : Position n → W) (hf : ParentType y eta f) :
    ((MME.RecursiveXHash.target (n := n) m).filter (fun a ↦
        MME.RecursiveXHash.block i a = y ∧
          Compatible (fullCell htotal a) boundary group mu f)).card *
        Nat.card {g : Position n → W // ParentType y eta g} ≤
      ((MME.RecursiveXHash.target (n := n) m).filter
        (fun a ↦ MME.RecursiveXHash.block i a = y)).card *
          compatibilityNumber boundary group mu := by sorry
