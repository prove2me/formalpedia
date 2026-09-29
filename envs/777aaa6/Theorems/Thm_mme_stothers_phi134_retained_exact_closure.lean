-- Prove2me | Theorems.Thm_mme_stothers_phi134_retained_exact_closure
-- name    : mme_stothers_phi134_retained_exact_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:24:06.373763+00:00
-- url     : https://prove2.me/theorems/759c8f5e-2e09-4a32-adbb-ce749d26b5d0
-- title:
--   $\Phi_{1,3,4}$ retained exact family is closed under supported mixing
-- statement:
--   Let $S\subseteq\mathbb Z/p\mathbb Z$ contain no nonconstant three-term arithmetic progression, and fix one affine hash state. If three retained exact $\Phi_{1,3,4}$ edges $x,y,z$ form a coordinatewise-supported cyclic mixture, then there is a retained exact edge $e$ combining their selected vertices:
--
--   $$
--   v_0(e)=v_0(x),\qquad v_1(e)=v_1(y),\qquad v_2(e)=v_2(z).
--   $$
--
--   Supported mixing first produces an exact edge with these vertices. The affine-progression identity says the three inherited labels satisfy $s_x+s_y=2s_z$. Progression-freeness forces $s_x=s_y=s_z$, so the mixed edge has one common allowed label and is retained. This is the dynamic closure hypothesis required by the generic type-2 isolation theorem.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Roy. Soc. Edinburgh Sect. A 143 (2013), 351–369, progression-free cyclic pruning in Lemma 3.3 (pp. 359–361), specialized to $\Phi_{1,3,4}$ in Lemma 5.1(iii) (p. 365); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open MME.StothersFourth.Phi134

set_option autoImplicit false

theorem mme_stothers_phi134_retained_exact_closure
    {p N alpha beta gamma delta : ℕ}
    (S : Finset (ZMod p))
    (hSfree : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a + b = 2 * c → a = c ∧ c = b)
    (q : HashState p N) :
    ∀ x ∈ retainedEdges p N alpha beta gamma delta S q,
      ∀ y ∈ retainedEdges p N alpha beta gamma delta S q,
        ∀ z ∈ retainedEdges p N alpha beta gamma delta S q,
          CyclicCoordinatewiseSupported x y z →
            ∃ e ∈ retainedEdges p N alpha beta gamma delta S q,
              cyclicModeWord e 0 = cyclicModeWord x 0 ∧
              cyclicModeWord e 1 = cyclicModeWord y 1 ∧
              cyclicModeWord e 2 = cyclicModeWord z 2 := by
  sorry
